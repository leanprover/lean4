#!/usr/bin/env python3

import subprocess
import sys
import json
from datetime import datetime, timedelta
from urllib.parse import urlencode
import argparse
import statistics

def get_items(query, item_type):
    items = []
    page = 1
    base_url = 'https://api.github.com/search/issues'
    while True:
        params = {'q': query, 'per_page': 100, 'page': page}
        url = f"{base_url}?{urlencode(params)}"
        # print(f"Fetching page {page} from URL: {url}")
        try:
            result = subprocess.run(['gh', 'api', url], capture_output=True, text=True)
            data = json.loads(result.stdout)
            if 'items' in data:
                items.extend(data['items'])
            else:
                print(f"Error fetching {item_type}: {data}")
                break
            if len(data['items']) < 100:
                break
            page += 1
        except Exception as e:
            print(f"Error fetching {item_type}: {e}")
            print(result.stdout)  # Print the JSON output for debugging
            break
    return items

def get_fro_team_members():
    try:
        result = subprocess.run(['gh', 'api', '-H', 'Accept: application/vnd.github.v3+json', '/orgs/leanprover/teams/fro/members'], capture_output=True, text=True)
        members = json.loads(result.stdout)
        return [member['login'] for member in members]
    except Exception as e:
        print(f"Error fetching team members: {e}")
        return []

def filter_items_by_members(items, members):
    return [item for item in items if item['user']['login'] in members or (item.get('closed_by') and item['closed_by']['login'] in members)]

def calculate_age_statistics(items):
    current_date = datetime.now()
    ages = [(current_date - datetime.strptime(item['created_at'], '%Y-%m-%dT%H:%M:%SZ')).days for item in items]
    average_age = sum(ages) / len(ages) if ages else 0
    median_age = statistics.median(ages) if ages else 0
    return average_age, median_age

def main():
    parser = argparse.ArgumentParser(description="Fetch and count GitHub issues or pull requests.")
    parser.add_argument("days", type=int, help="Number of days to look back")
    parser.add_argument("--fro", action="store_true", help="Filter by fro team members")
    parser.add_argument("--pr", action="store_true", help="Search pull requests instead of issues")
    
    args = parser.parse_args()

    since_date = (datetime.now() - timedelta(days=args.days)).strftime('%Y-%m-%dT%H:%M:%SZ')
    repo = "leanprover/lean4"
    item_type = "pr" if args.pr else "issue"
    item_name = "PRs" if args.pr else "Issues"

    created_not_closed_query = f'repo:{repo} is:{item_type} created:>{since_date} state:open'
    created_closed_query = f'repo:{repo} is:{item_type} created:>{since_date} state:closed'
    already_existing_closed_query = f'repo:{repo} is:{item_type} created:<={since_date} closed:>{since_date}'
    already_existing_not_closed_query = f'repo:{repo} is:{item_type} created:<={since_date} state:open'
    all_open_query = f'repo:{repo} is:{item_type} state:open'

    created_not_closed_items = get_items(created_not_closed_query, item_name)
    created_closed_items = get_items(created_closed_query, item_name)
    already_existing_closed_items = get_items(already_existing_closed_query, item_name)
    already_existing_not_closed_items = get_items(already_existing_not_closed_query, item_name)
    all_open_items = get_items(all_open_query, item_name)

    if args.fro:
        fro_members = get_fro_team_members()
        created_not_closed_items = filter_items_by_members(created_not_closed_items, fro_members)
        created_closed_items = filter_items_by_members(created_closed_items, fro_members)
        already_existing_closed_items = filter_items_by_members(already_existing_closed_items, fro_members)
        already_existing_not_closed_items = filter_items_by_members(already_existing_not_closed_items, fro_members)
        all_open_items = filter_items_by_members(all_open_items, fro_members)

    print(f"{item_name} created but not yet closed in the last {args.days} days: {len(created_not_closed_items)}")
    print(f"{item_name} created and closed in the last {args.days} days: {len(created_closed_items)}")
    print(f"{item_name} already existing and closed in the last {args.days} days: {len(already_existing_closed_items)}")
    print(f"{item_name} already existing and not yet closed in the last {args.days} days: {len(already_existing_not_closed_items)}")

    average_age, median_age = calculate_age_statistics(all_open_items)
    print(f"Average age of open {item_name}: {average_age:.2f} days")
    # print(f"Median age of open {item_name}: {median_age:.2f} days")

if __name__ == "__main__":
    main()