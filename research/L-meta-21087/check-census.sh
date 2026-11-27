set -eu
source work/run35/env.sh
cd work/21087/unrestricted
export LEAN_PATH="$PWD:$LEAN_PATH"
for mod in ProfileGroups $(seq -f 'TestGroup%g' 0 24) ProfileCensus; do
 [ ! -e ../stop ] && [ ! -e ../released ] && python -c "import json;assert json.load(open('../../current'))['gap']['id']=='L-meta-21087'" || exit 1
 echo "$mod"
 lean -o "$mod.olean" "$mod.lean" > "$mod.log" 2>&1
done
