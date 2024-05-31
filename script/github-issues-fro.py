#!/usr/bin/env python3

import subprocess
import sys
import json
from datetime import datetime, timedelta
from urllib.parse import urlencode
import argparse
import calendar
import time
import statistics

# Reminder: Ensure you have `gh` CLI installed and authorized before running this script.
# Follow instructions from https://cli.github.com/ to set up `gh` and ensure it is authorized.

LABELS = ["bug", "feature", "RFC", "new-user-papercuts", "Lake"]

def get_items(query):
    items = []
    page = 1
    base_url = 'https://api.github.com/search/issues'
    retries = 0
    max_retries = 5
    while True:
        params = {'q': query, 'per_page': 100, 'page': page}
        url = f"{base_url}?{urlencode(params)}"
        # print(f"Fetching page {page} from URL: {url}")
        try:
            result = subprocess.run(['gh', 'api', url], capture_output=True, text=True)
            data = json.loads(result.stdout)
            if 'items' in data:
                items.extend(data['items'])
            elif 'message' in data and 'rate limit' in data['message'].lower():
                if retries < max_retries:
                    wait_time = (2 ** retries) * 60  # Exponential backoff
                    time.sleep(wait_time)
                    retries += 1
                    continue
                else:
                    print("Max retries exceeded. Exiting.")
                    break
            else:
                print(f"Error fetching data: {data}")
                break
            if len(data['items']) < 100:
                break
            page += 1
        except Exception as e:
            print(f"Error fetching data: {e}")
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

def calculate_average_time_to_close(closed_items):
    times_to_close = [(datetime.strptime(item['closed_at'], '%Y-%m-%dT%H:%M:%SZ') - datetime.strptime(item['created_at'], '%Y-%m-%dT%H:%M:%SZ')).days for item in closed_items]
    average_time_to_close = sum(times_to_close) / len(times_to_close) if times_to_close else 0
    return average_time_to_close

def parse_dates(date_args):
    if len(date_args) == 2:
        start_date = date_args[0]
        end_date = date_args[1]
    elif len(date_args) == 1:
        if len(date_args[0]) == 7:  # YYYY-MM format
            year, month = map(int, date_args[0].split('-'))
            start_date = f"{year}-{month:02d}-01"
            end_date = f"{year}-{month:02d}-{calendar.monthrange(year, month)[1]}"
        elif len(date_args[0]) == 4:  # YYYY format
            year = int(date_args[0])
            start_date = f"{year}-07-01"
            end_date = f"{year+1}-06-30"
        elif len(date_args[0]) == 6 and date_args[0][4] == 'Q':  # YYYYQn format
            year = int(date_args[0][:4])
            quarter = int(date_args[0][5])
            if quarter == 1:
                start_date = f"{year}-01-01"
                end_date = f"{year}-03-31"
            elif quarter == 2:
                start_date = f"{year}-04-01"
                end_date = f"{year}-06-30"
            elif quarter == 3:
                start_date = f"{year}-07-01"
                end_date = f"{year}-09-30"
            elif quarter == 4:
                start_date = f"{year}-10-01"
                end_date = f"{year}-12-31"
            else:
                raise ValueError("Invalid quarter format")
        else:
            raise ValueError("Invalid date format")
    else:
        raise ValueError("Invalid number of date arguments")

    return start_date, end_date

def split_date_range(start_date, end_date):
    start = datetime.strptime(start_date, '%Y-%m-%d')
    end = datetime.strptime(end_date, '%Y-%m-%d')
    date_ranges = []

    # Splitting into month-long windows to work around the GitHub search 1000 result limit.
    while start <= end:
        month_end = start + timedelta(days=calendar.monthrange(start.year, start.month)[1] - start.day)
        month_end = min(month_end, end)
        date_ranges.append((start.strftime('%Y-%m-%d'), month_end.strftime('%Y-%m-%d')))
        start = month_end + timedelta(days=1)

    return date_ranges

def main():
    parser = argparse.ArgumentParser(description="Fetch and count GitHub issues assigned to fro team members between two dates.")
    parser.add_argument("dates", type=str, nargs='+', help="Start and end dates in YYYY-MM-DD, YYYY-MM, YYYY-Qn, or YYYY format")

    args = parser.parse_args()
    start_date, end_date = parse_dates(args.dates)

    repo = "leanprover/lean4"

    date_ranges = split_date_range(start_date, end_date)

    fro_members = get_fro_team_members()
    fro_members.append("unassigned")  # Add "unassigned" for issues with no assignee

    label_headers = ", ".join([f"MTTR ({label})" for label in LABELS])
    print(f"# username, open issues, new issues, closed issues, MTTR (all), {label_headers}")

    for member in fro_members:
        open_issues_count = 0
        new_issues_count = 0
        closed_issues_count = 0
        total_time_to_close_issues = 0
        closed_issues = []
        label_times = {label: [] for label in LABELS}

        for start, end in date_ranges:
            if member == "unassigned":
                open_issues_query1 = f'repo:{repo} is:issue no:assignee state:open created:<={end}'
                open_issues_query2 = f'repo:{repo} is:issue no:assignee state:closed created:<={end} closed:>{end}'
                new_issues_query = f'repo:{repo} is:issue no:assignee created:{start}..{end}'
                closed_issues_query = f'repo:{repo} is:issue no:assignee closed:{start}..{end}'
            else:
                open_issues_query1 = f'repo:{repo} is:issue assignee:{member} state:open created:<={end}'
                open_issues_query2 = f'repo:{repo} is:issue assignee:{member} state:closed created:<={end} closed:>{end}'
                new_issues_query = f'repo:{repo} is:issue assignee:{member} created:{start}..{end}'
                closed_issues_query = f'repo:{repo} is:issue assignee:{member} closed:{start}..{end}'

            open_issues1 = get_items(open_issues_query1)
            open_issues2 = get_items(open_issues_query2)
            new_issues = get_items(new_issues_query)
            closed_issues_period = get_items(closed_issues_query)

            open_issues_count = len(open_issues1) + len(open_issues2)
            new_issues_count += len(new_issues)
            closed_issues_count += len(closed_issues_period)
            closed_issues.extend(closed_issues_period)

            for issue in closed_issues_period:
                time_to_close = (datetime.strptime(issue['closed_at'], '%Y-%m-%dT%H:%M:%SZ') - datetime.strptime(issue['created_at'], '%Y-%m-%dT%H:%M:%SZ')).days
                total_time_to_close_issues += time_to_close
                for label in LABELS:
                    if label in [l['name'] for l in issue['labels']]:
                        label_times[label].append(time_to_close)

        average_time_to_close_issues = total_time_to_close_issues / closed_issues_count if closed_issues_count else 0
        label_averages = {label: (sum(times) / len(times)) if times else 0 for label, times in label_times.items()}

        label_averages_str = ", ".join([f"{label_averages[label]:.2f}" for label in LABELS])
        print(f"{member},{open_issues_count},{new_issues_count},{closed_issues_count},{average_time_to_close_issues:.2f},{label_averages_str}")

if __name__ == "__main__":
    main()
