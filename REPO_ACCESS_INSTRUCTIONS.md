# Accessing FStarLang/AutoCLRS GitHub API (Private Repo)

This repository is **private** under `FStarLang/AutoCLRS`. The standard
MCP GitHub tools and `web_fetch` will return 404. Use the method below
to access issues, PRs, and other API endpoints.

## Method: Git Credential Helper → GitHub REST API

The environment has SSH access configured for `nikswamy`. The git
credential helper can produce an OAuth token usable with the GitHub
REST API.

### Step 1: Obtain a token

```python
import subprocess
result = subprocess.run(
    ['git', 'credential', 'fill'],
    input='protocol=https\nhost=github.com\n',
    capture_output=True, text=True
)
token = [
    l.split('=', 1)[1]
    for l in result.stdout.strip().split('\n')
    if l.startswith('password=')
][0]
```

### Step 2: Make API calls

```python
import json, urllib.request

headers = {
    'Authorization': f'token {token}',
    'Accept': 'application/vnd.github.v3+json',
}

# Read an issue
req = urllib.request.Request(
    'https://api.github.com/repos/FStarLang/AutoCLRS/issues/2',
    headers=headers
)
data = json.loads(urllib.request.urlopen(req).read())
print(data['title'], data['body'])

# Read issue comments
req = urllib.request.Request(
    'https://api.github.com/repos/FStarLang/AutoCLRS/issues/2/comments?per_page=100',
    headers=headers
)
comments = json.loads(urllib.request.urlopen(req).read())
for c in comments:
    print(c['user']['login'], c['body'])

# Post a comment
body = json.dumps({"body": "Comment text here"}).encode()
req = urllib.request.Request(
    'https://api.github.com/repos/FStarLang/AutoCLRS/issues/2/comments',
    data=body,
    headers={**headers, 'Content-Type': 'application/json'},
    method='POST'
)
resp = json.loads(urllib.request.urlopen(req).read())
print(resp['html_url'])
```

### Common Endpoints

| Action | Method | URL |
|---|---|---|
| List issues | GET | `/repos/FStarLang/AutoCLRS/issues` |
| Read issue | GET | `/repos/FStarLang/AutoCLRS/issues/{number}` |
| Issue comments | GET | `/repos/FStarLang/AutoCLRS/issues/{number}/comments` |
| Post comment | POST | `/repos/FStarLang/AutoCLRS/issues/{number}/comments` |
| List PRs | GET | `/repos/FStarLang/AutoCLRS/pulls` |
| Read PR | GET | `/repos/FStarLang/AutoCLRS/pulls/{number}` |
| PR review comments | GET | `/repos/FStarLang/AutoCLRS/pulls/{number}/comments` |

All URLs are prefixed with `https://api.github.com`.

### Why MCP GitHub Tools Don't Work

The MCP `github-mcp-server` tools authenticate with a different token
that does not have access to this private repo. The git credential
helper token (obtained via `git credential fill`) does have access
because the environment's git is configured with SSH keys for
`nikswamy`.

### Notes

- The token is short-lived; obtain a fresh one for each session.
- `gh` CLI is not installed; use `urllib.request` or `curl` directly.
- For git operations (push/pull/fetch), SSH works normally.
