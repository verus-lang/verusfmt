import sys
import re

rules = set([])
strs = set([])

with open(sys.argv[1]) as pest:
    for line in pest.readlines():
        match = re.search("(\w*) = .*{", line)
        if not match is None:
            rule_name = match.group(1)
            rules.add(rule_name)

        matches = re.findall("\"(.+?)\"", line)
        for match in matches:
            strs.add(match)

new_rules = {}
for s in sorted(strs):
    rule_name = s + "_str"
#    if s in rules:
#        rule_name += "_str" 
    rule = rule_name + f" = {{ \"{s}\" }}"
    print(rule)
    new_rules[s] = rule_name
    


with open(sys.argv[1]) as pest:
    for line in pest.readlines():
        for s,n in new_rules.items():
            if s[0].isalpha():
                src = f"\"{s}\""
                dst = f"{n}"
                line = line.replace(src, dst)
        print(line.rstrip('\n'))

