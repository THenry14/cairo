// TODO:
// 0. Use real costs
// 1. Other gas tokens
// 2. AP
// 3. Withdraw gas builtins.
// 4. refund gas

use cairo_lang_sierra::extensions::builtin_cost::CostTokenType;
use cairo_lang_sierra::extensions::core::{CoreLibfunc, CoreType};
use cairo_lang_sierra::extensions::ConcreteType;
use cairo_lang_sierra::ids::{ConcreteLibfuncId, ConcreteTypeId};
use cairo_lang_sierra::program::{Invocation, Program, Statement, StatementIdx};
use cairo_lang_sierra::program_registry::ProgramRegistry;
use cairo_lang_utils::ordered_hash_map::OrderedHashMap;
use cairo_lang_utils::unordered_hash_map::UnorderedHashMap;
use itertools::zip_eq;

use crate::core_libfunc_cost::ConstCost;
use crate::core_libfunc_cost_base::{core_libfunc_postcost, BranchCost, ComputeCostInfoProvider};
use crate::gas_info::GasInfo;
use crate::CostError;

type VariableValues = OrderedHashMap<(StatementIdx, CostTokenType), i64>;

pub struct ComputeCostInfoProviderImpl<'a> {
    registry: &'a ProgramRegistry<CoreType, CoreLibfunc>,
}
impl<'a> ComputeCostInfoProvider for ComputeCostInfoProviderImpl<'a> {
    fn type_size(&self, ty: &ConcreteTypeId) -> usize {
        // TODO: fix `as usize`.
        self.registry.get_type(ty).unwrap().info().size as usize
    }
}

trait CostTypeTrait: std::fmt::Debug + Default + Clone {
    fn max(values: impl Iterator<Item = Self>) -> Self;
}

impl CostTypeTrait for i32 {
    fn max(values: impl Iterator<Item = Self>) -> Self {
        values.max().unwrap_or_default()
    }
}

pub fn compute_costs(
    program: &Program,
    get_ap_change_fn: &dyn Fn(&StatementIdx) -> usize,
) -> Result<GasInfo, CostError> {
    type CostType = i32;
    let registry = ProgramRegistry::<CoreType, CoreLibfunc>::new(program)?;
    let info_provider = ComputeCostInfoProviderImpl { registry: &registry };
    let mut context = CostContext {
        program,
        costs: UnorderedHashMap::default(),
        get_cost_fn: &(|libfunc_id| {
            let core_libfunc = registry
                .get_libfunc(libfunc_id)
                .expect("Program registry creation would have already failed.");
            core_libfunc_postcost(core_libfunc, &info_provider)
        }),
        specific_cost_context: PostcostContext { get_ap_change_fn },
    };

    for i in 0..program.statements.len() {
        context.compute_wallet_at(&StatementIdx(i));
    }

    let mut variable_values = VariableValues::default();
    for i in 0..program.statements.len() {
        let specific_cost_context = &context.specific_cost_context;
        specific_cost_context.analyze_gas_statements(
            &context,
            &StatementIdx(i),
            &mut variable_values,
        );
    }
    let function_costs = program
        .funcs
        .iter()
        .map(|func| {
            (
                func.id.clone(),
                vec![(CostTokenType::Const, context.wallet_at(&func.entry_point) as i64)]
                    .into_iter()
                    .collect(),
            )
        })
        .collect();
    let gas_info = GasInfo { variable_values, function_costs };
    Ok(gas_info)
}

enum CostComputationStatus<CostType> {
    InProgress,
    Done(CostType),
}

struct BranchAlignInfo {
    statement_idx: StatementIdx,
    prev_statement_idx: StatementIdx,
}

trait CostContextTrait<CostType> {
    fn get_program(&self) -> &Program;
    fn get_cost(&self, libfunc_id: &ConcreteLibfuncId) -> Vec<BranchCost>;
    fn wallet_at(&self, idx: &StatementIdx) -> CostType;
}

trait SpecificCostContextTrait {
    type CostType: CostTypeTrait;

    /// Returns the required value for the wallet for each branch.
    fn get_branch_requirements(
        &self,
        context: &dyn CostContextTrait<Self::CostType>,
        idx: &StatementIdx,
        invocation: &Invocation,
        libfunc_cost: &[BranchCost],
    ) -> Vec<Self::CostType>;
}

struct CostContext<'a, SpecificCostContext: SpecificCostContextTrait> {
    program: &'a Program,
    get_cost_fn: &'a dyn Fn(&ConcreteLibfuncId) -> Vec<BranchCost>,
    /// The cost before executing a Sierra statement.
    costs: UnorderedHashMap<StatementIdx, CostComputationStatus<SpecificCostContext::CostType>>,
    specific_cost_context: SpecificCostContext,
}
impl<'a, SpecificCostContext: SpecificCostContextTrait>
    CostContextTrait<SpecificCostContext::CostType> for CostContext<'a, SpecificCostContext>
{
    fn get_program(&self) -> &Program {
        self.program
    }

    fn get_cost(&self, libfunc_id: &ConcreteLibfuncId) -> Vec<BranchCost> {
        (self.get_cost_fn)(libfunc_id)
    }

    /// Returns the required value in the wallet before executing statement `idx`.
    // TODO: There's an exception with branch_align - the function returns the wallet after the
    //   alignment.
    fn wallet_at(&self, idx: &StatementIdx) -> SpecificCostContext::CostType {
        match self.costs.get(idx) {
            Some(CostComputationStatus::Done(res)) => res.clone(),
            _ => {
                panic!("Wallet value for statement {idx} was not yet computed.")
            }
        }
    }
}

impl<'a, SpecificCostContext: SpecificCostContextTrait> CostContext<'a, SpecificCostContext> {
    /// Returns the required value in the wallet before executing statement `idx`.
    // TODO: There's an exception with branch_align - the function returns the wallet after the
    //   alignment.
    fn compute_wallet_at(&mut self, idx: &StatementIdx) -> SpecificCostContext::CostType {
        match self.costs.get(idx) {
            Some(CostComputationStatus::InProgress) => {
                panic!("Found an unexpected cycle during cost computation.")
            }
            Some(CostComputationStatus::Done(res)) => {
                return res.clone();
            }
            None => {}
        }

        // Mark the statement's computation as in-progress.
        self.costs.insert(*idx, CostComputationStatus::InProgress);

        let res = self.no_cache_compute_wallet_at(idx);

        // Update the cache with the result.
        self.costs.insert(*idx, CostComputationStatus::Done(res.clone()));
        println!("Cost of {idx} is {res:?}.");
        res
    }

    /// Same as [wallet_at], except that the cache is not used.
    ///
    /// Calls [wallet_at] to get the wallet value of the following instructions.
    fn no_cache_compute_wallet_at(&mut self, idx: &StatementIdx) -> SpecificCostContext::CostType {
        println!("Computing the cost of {idx}.");
        match &self.program.get_statement(idx).unwrap() {
            Statement::Return(_) => Default::default(),
            Statement::Invocation(invocation) => {
                let libfunc_cost: Vec<BranchCost> = self.get_cost(&invocation.libfunc_id);
                // For each branch, compute the required value for the wallet.
                let branch_requirements: Vec<SpecificCostContext::CostType> = self
                    .specific_cost_context
                    .get_branch_requirements(self, idx, invocation, &libfunc_cost);
                // The wallet value at the beginning of the statement is the maximal value
                // required by all the branches.
                SpecificCostContext::CostType::max(branch_requirements.into_iter())
            }
        }
    }
}

struct PostcostContext<'a> {
    get_ap_change_fn: &'a dyn Fn(&StatementIdx) -> usize,
}

impl<'a> SpecificCostContextTrait for PostcostContext<'a> {
    type CostType = i32;

    /// Returns the required value for the wallet for each branch.
    fn get_branch_requirements(
        &self,
        context: &dyn CostContextTrait<Self::CostType>,
        idx: &StatementIdx,
        invocation: &Invocation,
        libfunc_cost: &[BranchCost],
    ) -> Vec<i32> {
        zip_eq(&invocation.branches, libfunc_cost)
            .map(|(branch_info, branch_cost)| {
                let branch_cost = match &*branch_cost {
                    BranchCost::Constant(val) => val.cost(),
                    BranchCost::BranchAlign => {
                        let ap_change = (self.get_ap_change_fn)(idx);
                        if ap_change == 0 {
                            0
                        } else {
                            ConstCost { steps: 1, holes: ap_change as i32, range_checks: 0 }.cost()
                        }
                    }
                    BranchCost::FunctionCall { const_cost, function } => {
                        context.wallet_at(&function.entry_point) + const_cost.cost()
                    }
                    BranchCost::WithdrawGas { const_cost, success, with_builtins: _ } => {
                        let cost = const_cost.cost();
                        // TODO: with_builtins.
                        // If withdraw_gas succeeds, we don't need to take
                        // future_wallet_value into account, so we simply return.
                        if *success {
                            return cost;
                        }
                        cost
                    }
                    BranchCost::RedepositGas => todo!(),
                };
                let future_wallet_value = context.wallet_at(&idx.next(&branch_info.target));
                branch_cost + future_wallet_value
            })
            .collect()
    }
}

impl<'a> PostcostContext<'a> {
    fn analyze_gas_statements(
        &self,
        context: &CostContext<Self>,
        idx: &StatementIdx,
        variable_values: &mut VariableValues,
    ) {
        let Statement::Invocation(invocation) = &context.get_program().get_statement(idx).unwrap() else {
            return;
        };
        let libfunc_cost: Vec<BranchCost> = context.get_cost(&invocation.libfunc_id);
        let branch_requirements: Vec<i32> =
            self.get_branch_requirements(context, idx, invocation, &libfunc_cost);

        let wallet_value = context.wallet_at(idx);

        if invocation.branches.len() > 1 {
            for ((branch_info, branch_cost), branch_requirement) in
                zip_eq(zip_eq(&invocation.branches, &libfunc_cost), &branch_requirements)
            // TODO: zip_eq3?
            {
                let future_wallet_value = context.wallet_at(&idx.next(&branch_info.target));
                if let BranchCost::WithdrawGas { const_cost, success: true, with_builtins: _ } =
                    branch_cost
                {
                    // TODO: with_builtins.
                    let amount =
                        ((const_cost.cost() + future_wallet_value) as i64) - (wallet_value as i64);
                    // println!("Withdraw amount of {:?}: {}", idx, std::cmp::max(amount, 0));
                    // println!(
                    //     "Branch align of {:?}: {}",
                    //     idx.next(&branch_info.target),
                    //     // TODO: is this always 0? What happens if the other branch is
                    //     // really small?
                    //     std::cmp::max(-amount, 0)
                    // );
                    assert!(
                        variable_values
                            .insert((idx.clone(), CostTokenType::Const), std::cmp::max(amount, 0))
                            .is_none()
                    );
                    assert!(
                        variable_values
                            .insert(
                                (idx.next(&branch_info.target), CostTokenType::Const),
                                std::cmp::max(-amount, 0),
                            )
                            .is_none()
                    );
                } else {
                    // TODO: Consider checking this is indeed branch align.
                    // println!(
                    //     "Branch align {:?} = {}",
                    //     idx.next(&branch_info.target),
                    //     wallet_value - branch_requirement
                    // );
                    assert!(
                        variable_values
                            .insert(
                                (idx.next(&branch_info.target), CostTokenType::Const),
                                (wallet_value - branch_requirement) as i64,
                            )
                            .is_none()
                    );
                }
            }
        }
    }
}
