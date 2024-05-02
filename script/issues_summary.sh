#!/bin/bash

# https://chat.openai.com/share/7469c7c3-aceb-4d80-aee5-62982e1f1538

# Output CSV Header
echo '"Issue URL","Title","Days Since Creation","Days Since Last Update","Total Reactions","Assignee","Labels"'

# Get the current date in YYYY-MM-DD format
today=$(date +%Y-%m-%d)

# Fetch only open issues (excluding PRs and closed issues) from the repository 'leanprover/lean4'
issues=$(gh api repos/leanprover/lean4/issues --paginate --jq '.[] | select(.pull_request == null and .state == "open") | {url: .html_url, title: .title, created_at: (.created_at | split("T")[0]), updated_at: (.updated_at | split("T")[0]), number: .number, assignee: (.assignee.login // ""), labels: [.labels[].name] | join(",")}')

# Process each JSON object
echo "$issues" | while IFS= read -r issue; do
    # Extract fields from JSON
    url=$(echo "$issue" | jq -r '.url')
    title=$(echo "$issue" | jq -r '.title')
    created_at=$(echo "$issue" | jq -r '.created_at')
    updated_at=$(echo "$issue" | jq -r '.updated_at')
    issue_number=$(echo "$issue" | jq -r '.number')
    assignee=$(echo "$issue" | jq -r '.assignee')
    labels=$(echo "$issue" | jq -r '.labels')

    # Calculate days since creation and update using macOS compatible date calculation
    days_since_created=$(( ($(date -jf "%Y-%m-%d" "$today" +%s) - $(date -jf "%Y-%m-%d" "$created_at" +%s)) / 86400 ))
    days_since_updated=$(( ($(date -jf "%Y-%m-%d" "$today" +%s) - $(date -jf "%Y-%m-%d" "$updated_at" +%s)) / 86400 ))

    # Fetch the total number of reactions for each issue
    reaction_data=$(gh api repos/leanprover/lean4/issues/$issue_number/reactions --paginate --jq 'length' 2>&1)
    if [[ $reaction_data == *"Not Found"* ]]; then
        total_reactions="Error fetching reactions"
    else
        total_reactions=$reaction_data
    fi

    # Format output as CSV by escaping quotes and delimiting with commas
    echo "\"$url\",\"${title//\"/\"\"}\",\"$days_since_created\",\"$days_since_updated\",\"$total_reactions\",\"$assignee\",\"$labels\""
done
