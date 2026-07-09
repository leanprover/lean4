#!/usr/bin/env python3
#
# Embeds each failed test's captured output (`<system-out>`) into its
# `<failure>`/`<error>` element of a ctest JUnit XML file, in place.
# JUnit renderers such as test-summary/action display the failure element's
# text but ignore `<system-out>`, so without this step the CI test summary
# shows only the names of failed tests.

import sys
import xml.etree.ElementTree as ET

# caps to keep the rendered summary below GitHub's 1MiB step summary limit
MAX_OUTPUT_PER_TEST = 8000
MAX_OUTPUT_TOTAL = 400000

def truncate(text, limit):
    if len(text) <= limit:
        return text
    half = limit // 2
    return text[:half] + "\n[... output truncated ...]\n" + text[len(text) - half:]

def main():
    if len(sys.argv) != 2:
        sys.exit(f"usage: {sys.argv[0]} <test-results.xml>")
    path = sys.argv[1]
    try:
        tree = ET.parse(path)
    except FileNotFoundError:
        print(f"'{path}' does not exist, nothing to do")
        return
    budget = MAX_OUTPUT_TOTAL
    for testcase in tree.getroot().iter("testcase"):
        for tag in ("failure", "error"):
            elem = testcase.find(tag)
            if elem is None or elem.text:
                continue
            limit = min(MAX_OUTPUT_PER_TEST, budget)
            if limit < 500:
                print("total output budget exhausted, skipping remaining failures")
                tree.write(path, encoding="UTF-8", xml_declaration=True)
                return
            out = truncate((testcase.findtext("system-out") or "").strip("\n"), limit)
            if not out:
                continue
            elem.text = out
            budget -= len(out)
    tree.write(path, encoding="UTF-8", xml_declaration=True)

if __name__ == "__main__":
    main()
