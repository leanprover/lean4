#!/usr/bin/env python3

import argparse
import json
from pathlib import Path

OUTFILE = Path() / "measurements.jsonl"

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=f"Combine duplicated measurements in {OUTFILE.name} the way radar does, by summing their values."
    )
    args = parser.parse_args()

    values: dict[str, float] = {}
    units: dict[str, str | None] = {}

    with open(OUTFILE, "r") as f:
        for line in f:
            data = json.loads(line)
            metric = data["metric"]
            values[metric] = values.get(metric, 0) + data["value"]
            units[metric] = data.get("unit")

    with open(OUTFILE, "w") as f:
        for metric, value in values.items():
            unit = units.get(metric)
            data = {"metric": metric, "value": value}
            if unit is not None:
                data["unit"] = unit
            f.write(f"{json.dumps(data)}\n")
