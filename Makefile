tutorial:
	pandoc README.md --template=template.latex -V documentclass=lipics-v2021 --filter pandoc-include-code  -No /tmp/tutorial.pdf
