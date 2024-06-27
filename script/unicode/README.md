# Unicode

This tool is used to generate Unicode tables for fast and memory efficient lookup of character properties. It uses a skip list (inspired from Rust).
The program is meant to be run when we want to update to a newer version of Unicode. The code generation program can be run as `lake exe generate_tables`.
The generated table can be verified as `lake exe verify_tables`.
