import os
import sys
import json
import urllib.request
import urllib.parse
import base64
import datetime

def main():
    # Resolve paths relative to this script
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_root = os.path.dirname(os.path.dirname(script_dir))
    token_file = os.path.join(project_root, ".sonarqube_token")
    
    if not os.path.exists(token_file):
        print(f"Error: Token file not found at {token_file}")
        sys.exit(1)
        
    with open(token_file, "r") as f:
        token = f.read().strip()
        
    if not token:
        print("Error: Token file is empty")
        sys.exit(1)
        
    project_key = "groupId:2chance"
    
    # Authenticate via Basic Auth (token as username, blank password)
    auth_str = f"{token}:"
    auth_b64 = base64.b64encode(auth_str.encode('utf-8')).decode('utf-8')
    
    page = 1
    page_size = 500
    all_issues = []
    
    print("Fetching all issues from SonarQube API...")
    while True:
        url = f"http://localhost:9000/api/issues/search?componentKeys={urllib.parse.quote(project_key)}&ps={page_size}&p={page}"
        req = urllib.request.Request(url)
        req.add_header("Authorization", f"Basic {auth_b64}")
        
        try:
            with urllib.request.urlopen(req) as response:
                data = json.loads(response.read().decode('utf-8'))
        except Exception as e:
            print(f"Error: Failed to fetch issues from SonarQube: {e}")
            sys.exit(1)
            
        issues = data.get("issues", [])
        all_issues.extend(issues)
        
        paging = data.get("paging", {})
        total = paging.get("total", 0)
        
        if len(all_issues) >= total or not issues:
            break
            
        page += 1
        
    # Filter for Creedengo (eco-design) issues only
    creedengo_issues = []
    for issue in all_issues:
        rule = issue.get("rule", "")
        if "creedengo" in rule or "ecoCode" in rule or rule.startswith("creedengo-java:"):
            creedengo_issues.append(issue)
            
    if not creedengo_issues:
        print("No Creedengo eco-design issues found or project has not been analyzed yet.")
        sys.exit(0)
        
    # Group issues by rule key for a summary table
    by_rule = {}
    for issue in creedengo_issues:
        rule = issue.get("rule", "")
        by_rule.setdefault(rule, []).append(issue)
        
    # Generate the Markdown content
    report_content = []
    report_content.append("# Creedengo (Eco-Design) Violations Report\n")
    report_content.append(f"Generated on: **{datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}**\n")
    report_content.append(f"Total Creedengo issues found: **{len(creedengo_issues)}**\n\n")
    
    report_content.append("## Summary by Rule\n\n")
    report_content.append("| Rule | Description | Count |\n")
    report_content.append("|---|---|---|\n")
    for rule, rule_issues in sorted(by_rule.items(), key=lambda x: len(x[1]), reverse=True):
        msg_sample = rule_issues[0].get("message", "")
        if len(msg_sample) > 60:
            msg_sample = msg_sample[:57] + "..."
        report_content.append(f"| `{rule}` | {msg_sample} | {len(rule_issues)} |\n")
        
    report_content.append("\n## Detailed Issues List\n\n")
    report_content.append("| # | File | Line | Rule | Message | Severity |\n")
    report_content.append("|---|------|------|------|---------|----------|\n")
    
    for idx, issue in enumerate(creedengo_issues, 1):
        component = issue.get("component", "")
        file_path = component.split(":")[-1] if ":" in component else component
        line = issue.get("line", "N/A")
        rule = issue.get("rule", "")
        message = issue.get("message", "").replace("|", "\\|")
        severity = issue.get("severity", "")
        report_content.append(f"| {idx} | `{file_path}` | {line} | `{rule}` | {message} | {severity} |\n")
        
    markdown_text = "".join(report_content)
    
    # Save 1: Main report file in reports/creedengo_only_issues_report.md
    report_path = os.path.join(project_root, "reports", "creedengo_only_issues_report.md")
    os.makedirs(os.path.dirname(report_path), exist_ok=True)
    with open(report_path, "w", encoding="utf-8") as rf:
        rf.write(markdown_text)
    print(f"Report successfully generated at: {report_path}")
    
    # Save 2: Timestamped log under src/sonarqube-creedengo/creedengo_logs/
    timestamp = datetime.datetime.now().strftime("%Y_%m_%d_%H_%M_%S")
    log_dir = os.path.join(script_dir, "creedengo_logs")
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f"log_creedengo_analysis_{timestamp}.md")
    with open(log_path, "w", encoding="utf-8") as lf:
        lf.write(markdown_text)
    print(f"Timestamped log successfully generated at: {log_path}")

if __name__ == "__main__":
    main()
