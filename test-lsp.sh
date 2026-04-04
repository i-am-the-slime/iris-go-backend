#!/bin/bash

# Test LSP communication
MSG='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{},"rootUri":"file:///Users/mark/Developer/purescript-analyzer/purescript-test-project"}}'
LEN=${#MSG}

# Send proper LSP headers
printf "Content-Length: %d\r\n\r\n%s" $LEN "$MSG" | purescript-analyzer --stdio