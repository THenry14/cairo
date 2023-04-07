// TODO:
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
use crate::core_libfunc_cost_base::{
    core_libfunc_postcost, BranchCost, ComputeCostInfoProvider, PreCost,
};
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

trait CostTypeTrait: std::fmt::Debug + Default + Clone + Eq {
    fn max(values: impl Iterator<Item = Self>) -> Self;
}

impl CostTypeTrait for i32 {
    fn max(values: impl Iterator<Item = Self>) -> Self {
        values.max().unwrap_or_default()
    }
}
impl CostTypeTrait for PreCost {
    fn max(values: impl Iterator<Item = Self>) -> Self {
        let mut res = Self::default();
        for value in values {
            for (token_type, val) in value.0 {
                res.0.insert(token_type, std::cmp::max(*res.0.get(&token_type).unwrap_or(&0), val));
            }
        }
        res
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
    };
    let specific_cost_context = PostcostContext { get_ap_change_fn };

    for i in 0..program.statements.len() {
        context.compute_wallet_at(&StatementIdx(i), &specific_cost_context);
    }

    let mut variable_values = VariableValues::default();
    for i in 0..program.statements.len() {
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

pub fn compute_precost_info(program: &Program) -> Result<GasInfo, CostError> {
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
    };
    let specific_cost_context = PreCostContext {};

    for i in 0..program.statements.len() {
        context.compute_wallet_at(&StatementIdx(i), &specific_cost_context);
    }

    let mut variable_values = VariableValues::default();
    for i in 0..program.statements.len() {
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
            let res = context.wallet_at(&func.entry_point).0;
            let res_i64 =
                res.into_iter().map(|(token_type, val)| (token_type, val as i64)).collect();
            // let res_with_all_token_types = CostTokenType::iter_precost()
            //     .map(|token_type| (*token_type, *res.get(token_type).unwrap_or(&0) as i64))
            //     .collect();
            (func.id.clone(), res_i64)
        })
        .collect();
    let gas_info = GasInfo { variable_values, function_costs };
    Ok(gas_info)
}

enum CostComputationStatus<CostType> {
    InProgress {
        // To allow cycles that do not use builtins, when we see a cycle, we "guess" that the wallet
        // value is zero. When the computation ends, we verify that the result is indeed zero.
        zero: bool,
    },
    Done(CostType),
}

trait CostContextTrait<CostType> {
    fn get_program(&self) -> &Program;
    fn get_cost(&self, libfunc_id: &ConcreteLibfuncId) -> Vec<BranchCost>;
    fn wallet_at(&self, idx: &StatementIdx) -> CostType;
}

trait SpecificCostContextTrait<CostType: CostTypeTrait> {
    /// Returns the required value for the wallet for each branch.
    fn get_branch_requirements(
        &self,
        wallet_at_fn: &mut dyn FnMut(&StatementIdx) -> CostType,
        idx: &StatementIdx,
        invocation: &Invocation,
        libfunc_cost: &[BranchCost],
    ) -> Vec<CostType>;
}

struct CostContext<'a, CostType> {
    program: &'a Program,
    get_cost_fn: &'a dyn Fn(&ConcreteLibfuncId) -> Vec<BranchCost>,
    /// The cost before executing a Sierra statement.
    costs: UnorderedHashMap<StatementIdx, CostComputationStatus<CostType>>,
}
impl<'a, CostType: CostTypeTrait> CostContextTrait<CostType> for CostContext<'a, CostType> {
    fn get_program(&self) -> &Program {
        self.program
    }

    fn get_cost(&self, libfunc_id: &ConcreteLibfuncId) -> Vec<BranchCost> {
        (self.get_cost_fn)(libfunc_id)
    }

    /// Returns the required value in the wallet before executing statement `idx`.
    // TODO: There's an exception with branch_align - the function returns the wallet after the
    //   alignment.
    fn wallet_at(&self, idx: &StatementIdx) -> CostType {
        match self.costs.get(idx) {
            Some(CostComputationStatus::Done(res)) => res.clone(),
            _ => {
                panic!("Wallet value for statement {idx} was not yet computed.")
            }
        }
    }
}

impl<'a, CostType: CostTypeTrait> CostContext<'a, CostType> {
    /// Returns the required value in the wallet before executing statement `idx`.
    // TODO: There's an exception with branch_align - the function returns the wallet after the
    //   alignment.
    fn compute_wallet_at<SpecificCostContext: SpecificCostContextTrait<CostType>>(
        &mut self,
        idx: &StatementIdx,
        specific_cost_context: &SpecificCostContext,
    ) -> CostType {
        match self.costs.get_mut(idx) {
            Some(CostComputationStatus::InProgress { zero }) => {
                // When a cycle is found, change the status [CostComputationStatus::Zero] in
                // order to force the wallet value to be zero.
                *zero = true;
                return CostType::default();
            }
            Some(CostComputationStatus::Done(res)) => {
                return res.clone();
            }
            None => {}
        }

        // Mark the statement's computation as in-progress.
        self.costs.insert(*idx, CostComputationStatus::InProgress { zero: false });

        // Compute the value.
        let res = self.no_cache_compute_wallet_at(idx, specific_cost_context);

        // Check if the status has changed to [CostComputationStatus::InProgressZero].
        if let Some(CostComputationStatus::InProgress { zero }) = self.costs.get(idx) {
            if *zero {
                println!("HERE"); // TODO
                assert!(
                    res == CostType::default(),
                    "Found an unexpected cycle during cost computation."
                )
            }
        } else {
            panic!("Unexpected CostComputationStatus.")
        }

        // Update the cache with the result.
        self.costs.insert(*idx, CostComputationStatus::Done(res.clone()));
        println!("Cost of {idx} is {res:?}.");
        res
    }

    /// Same as [wallet_at], except that the cache is not used.
    ///
    /// Calls [wallet_at] to get the wallet value of the following instructions.
    fn no_cache_compute_wallet_at<SpecificCostContext: SpecificCostContextTrait<CostType>>(
        &mut self,
        idx: &StatementIdx,
        specific_cost_context: &SpecificCostContext,
    ) -> CostType {
        match &self.program.get_statement(idx).unwrap() {
            Statement::Return(_) => Default::default(),
            Statement::Invocation(invocation) => {
                let libfunc_cost: Vec<BranchCost> = self.get_cost(&invocation.libfunc_id);

                // For each branch, compute the required value for the wallet.
                let branch_requirements: Vec<CostType> = specific_cost_context
                    .get_branch_requirements(
                        &mut |statement_idx| {
                            self.compute_wallet_at(statement_idx, specific_cost_context)
                        },
                        idx,
                        invocation,
                        &libfunc_cost,
                    );

                // The wallet value at the beginning of the statement is the maximal value
                // required by all the branches.
                CostType::max(branch_requirements.into_iter())
            }
        }
    }
}

struct PostcostContext<'a> {
    get_ap_change_fn: &'a dyn Fn(&StatementIdx) -> usize,
}

impl<'a> SpecificCostContextTrait<i32> for PostcostContext<'a> {
    /// Returns the required value for the wallet for each branch.
    fn get_branch_requirements(
        &self,
        wallet_at_fn: &mut dyn FnMut(&StatementIdx) -> i32,
        idx: &StatementIdx,
        invocation: &Invocation,
        libfunc_cost: &[BranchCost],
    ) -> Vec<i32> {
        zip_eq(&invocation.branches, libfunc_cost)
            .map(|(branch_info, branch_cost)| {
                let branch_cost = match &*branch_cost {
                    BranchCost::Constant { const_cost, pre_cost: _ } => const_cost.cost(),
                    BranchCost::BranchAlign => {
                        let ap_change = (self.get_ap_change_fn)(idx);
                        if ap_change == 0 {
                            0
                        } else {
                            ConstCost { steps: 1, holes: ap_change as i32, range_checks: 0 }.cost()
                        }
                    }
                    BranchCost::FunctionCall { const_cost, function } => {
                        wallet_at_fn(&function.entry_point) + const_cost.cost()
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
                let future_wallet_value = wallet_at_fn(&idx.next(&branch_info.target));
                branch_cost + future_wallet_value
            })
            .collect()
    }
}

impl<'a> PostcostContext<'a> {
    fn analyze_gas_statements(
        &self,
        context: &CostContext<i32>,
        idx: &StatementIdx,
        variable_values: &mut VariableValues,
    ) {
        let Statement::Invocation(invocation) = &context.get_program().get_statement(idx).unwrap() else {
            return;
        };
        let libfunc_cost: Vec<BranchCost> = context.get_cost(&invocation.libfunc_id);
        let branch_requirements: Vec<i32> = self.get_branch_requirements(
            &mut |statement_idx| context.wallet_at(statement_idx),
            idx,
            invocation,
            &libfunc_cost,
        );

        let wallet_value = context.wallet_at(idx);

        if invocation.branches.len() > 1 {
            // TODO: zip_eq3?
            for ((branch_info, branch_cost), branch_requirement) in
                zip_eq(zip_eq(&invocation.branches, &libfunc_cost), &branch_requirements)
            {
                let future_wallet_value = context.wallet_at(&idx.next(&branch_info.target));
                if let BranchCost::WithdrawGas { const_cost, success: true, with_builtins: _ } =
                    branch_cost
                {
                    // TODO: with_builtins.
                    let amount =
                        ((const_cost.cost() + future_wallet_value) as i64) - (wallet_value as i64);
                    assert!(variable_values
                        .insert((idx.clone(), CostTokenType::Const), std::cmp::max(amount, 0))
                        .is_none());
                    assert!(variable_values
                        .insert(
                            (idx.next(&branch_info.target), CostTokenType::Const),
                            std::cmp::max(-amount, 0),
                        )
                        .is_none());
                } else {
                    // TODO: Consider checking this is indeed branch align.
                    assert!(variable_values
                        .insert(
                            (idx.next(&branch_info.target), CostTokenType::Const),
                            (wallet_value - branch_requirement) as i64,
                        )
                        .is_none());
                }
            }
        }
    }
}

struct PreCostContext {}

impl SpecificCostContextTrait<PreCost> for PreCostContext {
    /// Returns the required value for the wallet for each branch.
    fn get_branch_requirements(
        &self,
        wallet_at_fn: &mut dyn FnMut(&StatementIdx) -> PreCost,
        idx: &StatementIdx,
        invocation: &Invocation,
        libfunc_cost: &[BranchCost],
    ) -> Vec<PreCost> {
        zip_eq(&invocation.branches, libfunc_cost)
            .map(|(branch_info, branch_cost)| {
                let branch_cost = match &*branch_cost {
                    BranchCost::Constant { const_cost: _, pre_cost } => pre_cost.clone(),
                    BranchCost::BranchAlign => Default::default(),
                    BranchCost::FunctionCall { const_cost: _, function } => {
                        wallet_at_fn(&function.entry_point)
                    }
                    BranchCost::WithdrawGas { const_cost: _, success, with_builtins } => {
                        if *with_builtins && *success {
                            // If withdraw_gas succeeds, we don't need to take
                            // future_wallet_value into account, so we simply return.
                            return Default::default();
                        } else {
                            Default::default()
                        }
                    }
                    BranchCost::RedepositGas => todo!(),
                };
                let future_wallet_value = wallet_at_fn(&idx.next(&branch_info.target));
                branch_cost + future_wallet_value
            })
            .collect()
    }
}

impl PreCostContext {
    fn analyze_gas_statements(
        &self,
        context: &CostContext<PreCost>,
        idx: &StatementIdx,
        variable_values: &mut VariableValues,
    ) {
        let Statement::Invocation(invocation) = &context.get_program().get_statement(idx).unwrap() else {
            return;
        };
        let libfunc_cost: Vec<BranchCost> = context.get_cost(&invocation.libfunc_id);
        let branch_requirements: Vec<PreCost> = self.get_branch_requirements(
            &mut |statement_idx| context.wallet_at(statement_idx),
            idx,
            invocation,
            &libfunc_cost,
        );

        let wallet_value = context.wallet_at(idx);

        if invocation.branches.len() > 1 {
            // TODO: zip_eq3?
            for ((branch_info, branch_cost), branch_requirement) in
                zip_eq(zip_eq(&invocation.branches, &libfunc_cost), &branch_requirements)
            {
                let future_wallet_value = context.wallet_at(&idx.next(&branch_info.target));
                if let BranchCost::WithdrawGas {
                    const_cost: _,
                    success: true,
                    with_builtins: true,
                } = branch_cost
                {
                    // TODO: with_builtins.
                    let res = (future_wallet_value - wallet_value.clone()).0;
                    for token_type in CostTokenType::iter_precost() {
                        let amount = *res.get(token_type).unwrap_or(&0) as i64;
                        assert!(variable_values
                            .insert((idx.clone(), *token_type), std::cmp::max(amount, 0))
                            .is_none());
                        assert!(variable_values
                            .insert(
                                (idx.next(&branch_info.target), *token_type),
                                std::cmp::max(-amount, 0),
                            )
                            .is_none());
                    }
                } else {
                    // TODO: Consider checking this is indeed branch align.
                    let res = (wallet_value.clone() - branch_requirement.clone()).0;
                    for token_type in CostTokenType::iter_precost() {
                        assert!(variable_values
                            .insert(
                                (idx.next(&branch_info.target), *token_type),
                                *res.get(token_type).unwrap_or(&0) as i64,
                            )
                            .is_none());
                    }
                }
            }
        }
    }
}
