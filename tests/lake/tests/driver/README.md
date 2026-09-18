# Multiple Test Drivers Implementation

This directory contains tests for the multiple test drivers feature implemented for Lake issue #6314.

## Files Added

- `multiple.toml` / `multiple.lean`: Configuration files demonstrating multiple test drivers using only libraries
- `mixed.toml` / `mixed.lean`: Configuration files demonstrating both `testDriver` and `testDrivers` working together
- `simple.toml`: Simple test case with a single driver using the new `testDrivers` syntax
- `Lib1.lean` / `Lib2.lean`: Test library files for the multiple drivers tests
- `Main.lean`: Executable entry point for mixed testing scenarios

## Implementation Details

The multiple test drivers feature has been implemented with the following changes:

### 1. Configuration Support

- Added `testDrivers : Array String := #[]` field to `PackageConfig`
- Added corresponding field to `Package` structure
- Updated TOML schema to support the `testDrivers` field
- Added documentation to README.md

### 2. Execution Logic

- Created `Package.runSingleTestDriver` helper function to execute individual drivers
- Updated `Package.test` function to handle both `testDriver` and `testDrivers` fields
- Drivers are executed in sequence: first `testDriver` (if specified), then each driver in `testDrivers`
- First non-zero exit code is returned immediately (fail-fast behavior)

### 3. Backward Compatibility

- Existing `testDriver` functionality remains unchanged
- New `testDrivers` field is optional and defaults to empty array
- Both fields can be used together for maximum flexibility

### 4. Test Coverage

- Tests demonstrate multiple library drivers
- Tests demonstrate mixed driver types (library + executable)
- Tests show both Lean and TOML configuration formats
- Existing driver validation tests remain functional

## Expected Behavior

When `lake test` is run with multiple drivers configured:

1. If `testDriver` is specified, it runs first
2. Each driver in `testDrivers` runs in sequence
3. For library drivers: the library is built
4. For executable drivers: the executable is built and executed
5. For script drivers: the script is executed
6. If any driver returns a non-zero exit code, execution stops and that code is returned
7. If all drivers succeed, `lake test` returns 0

## Usage Examples

See the example configurations in this directory and the updated README.md for usage patterns.