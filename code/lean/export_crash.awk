# Exit status 0 when a Comparator log shows the lean4export crash that one retry covers: the line
# "uncaught exception: Child exited with 139" after an "Exporting #[" line, and no line of a kernel run.
# Read by code/lean/comparator.sh (mode pass); the job comparator of .github/workflows/ci.yml applies the same rule.
# Usage: awk -f code/lean/export_crash.awk LOG
{ sub(/\r$/, "") }
/^Exporting #\[/ { exported = 1 }
exported && /^uncaught exception: Child exited with 139$/ { crashed = 1 }
/kernel on solution|kernel accepts the solution|kernel rejects the solution/ { kernel = 1 }
END { exit !(crashed && !kernel) }
