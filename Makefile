tutorial:
	pandoc README.md --template=template.latex --filter pandoc-include-code  -o /tmp/tutorial.pdf
