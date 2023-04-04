#!/usr/bin/env node
// @ts-check

const { stdin } = process;

// From https://github.com/sindresorhus/get-stdin/blob/main/index.js
async function getStdin() {
    let result = "";

    if (stdin.isTTY) {
        return result;
    }

    stdin.setEncoding("utf8");

    for await (const chunk of stdin) {
        result += chunk;
    }

    return result;
}

async function main() {
    const stdinData = await getStdin();
    console.log("stdin:", stdinData);

    /**
     * @type string[]
     **/
    const filesChanged = JSON.parse(stdinData);
    console.log("filesChanged:", filesChanged);

    const jobsToRun = [];

    add_crate_jobs(filesChanged, "cairo-lang-casm", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-compiler", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-debug", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-defs", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-diagnostics", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-eq-solver", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-filesystem", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-formatter", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-language-server", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-lowering", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-parser", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-plugins", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-proc_macros", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-project", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-runner", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-semantic", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-sierra", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-sierra-ap-change", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-sierra-gas", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-sierra-generator", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-sierra-to-casm", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-starknet", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-syntax", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-syntax-codegen", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-test-runner", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-test-utils", jobsToRun);
    add_crate_jobs(filesChanged, "cairo-lang-utils", jobsToRun);

    if (
        filesChanged.findIndex((fileChanged) =>
            fileChanged.endsWith(".rs")
        ) != -1
    ) {
        jobsToRun.push("-rustfmt-");
    }

    console.log("jobsToRun:", jobsToRun);
    console.log("::set-output name=jobs::" + jobsToRun.join());
}

async function add_crate_jobs(filesChanged, crate_name, jobsToRun) {
    if (
        filesChanged.findIndex((fileChanged) =>
            fileChanged.startsWith("crates/" + crate_name) && !fileChanged.includes("test")
        ) != -1
    ) {
        jobsToRun.push("-" + crate_name + "-");
    } else if (
        filesChanged.findIndex((fileChanged) =>
            fileChanged.startsWith("crates/" + crate_name)
        ) != -1
    ) {
        jobsToRun.push("-" + crate_name + "-test-only-");
    }
}

main().then(function () {
    console.log("Done");
});
