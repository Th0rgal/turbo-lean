pub const ORIGINAL_OPTIONS: &[(&str, &str)] = &[
    ("debug.skipKernelTC", "true"),
    ("debug.skipKernelTC", "false"),
    ("debug.byAsSorry", "true"),
    ("debug.proofAsSorry", "true"),
    ("debug.terminalTacticsAsSorry", "true"),
    ("debug.futureUnsafeOption", "true"),
    ("warn.sorry", "false"),
    ("warn.sorry", "0"),
    ("warn.sorry", "1"),
    ("warn.sorry", "False"),
    ("warn.sorry", "off"),
    ("warn.sorry", "TRUE"),
    ("stderrAsMessages", "false"),
    ("stderrAsMessages", "true"),
    ("internal.cmdlineSnapshots", "true"),
    ("internal.futureUnsafeOption", "false"),
];
// Old-head positive cases that main deliberately restricts. Keep them as regressions.
pub const RESTRICTED_OPTIONS: &[(&str, &str)] = &[
    ("pp.all", "true"),
    ("pp.raw", "true"),
    ("pp.maxSteps", "0"),
    ("Elab.async", "false"),
];
pub const GOOD_OPTIONS: &[(&str, &str)] = &[
    ("maxHeartbeats", "400000"),
    ("autoImplicit", "false"),
    ("pp.unicode.fun", "true"),
    ("pp.mvars.anonymous", "false"),
    ("linter.unusedVariables", "false"),
    ("warn.sorry", "true"),
];
pub const FIELDS: &[&str] = &["moreLeanArgs", "weakLeanArgs", "leanOptions"];
pub const SCOPES: &[&str] = &["package", "lean_lib", "lean_exe"];
pub const PREFIXES: &[&str] = &["", "weak.", "weak.weak."];

pub fn lakefile(format: &str, scope: &str, field: &str, key: &str, value: &str) -> String {
    let literal = if matches!(value, "true" | "false") || value.parse::<u64>().is_ok() {
        value.to_string()
    } else {
        format!("{value:?}")
    };
    let arg = format!("-D{key}={value}");
    if format == "lean" {
        let value = if field == "leanOptions" {
            format!("#[⟨`{key}, {literal}⟩]")
        } else {
            format!("#[{arg:?}]")
        };
        let headers = ["package fixture", "lean_lib Bad", "lean_exe Main"];
        let mut out = "import Lake\nopen Lake DSL\n".to_string();
        for (s, header) in SCOPES.iter().zip(headers) {
            out += header;
            if *s == scope {
                out += &format!(" where\n  {field} := {value}");
            }
            out += "\n";
        }
        out
    } else {
        let value = if field == "leanOptions" {
            format!("{{ {key} = {literal} }}")
        } else {
            format!("[{arg:?}]")
        };
        let headers = [
            "name = \"fixture\"",
            "[[lean_lib]]\nname = \"Bad\"",
            "[[lean_exe]]\nname = \"Main\"",
        ];
        let mut out = String::new();
        for (s, header) in SCOPES.iter().zip(headers) {
            out += header;
            out += "\n";
            if *s == scope {
                out += &format!("{field} = {value}\n");
            }
        }
        out
    }
}

// Preserve the original 864-case matrix, including the safe false spelling.
pub fn original_case_allowed(name: &str, value: &str, prefix: &str) -> bool {
    name == "debug.skipKernelTC" && value == "false" && matches!(prefix, "" | "weak.")
}
