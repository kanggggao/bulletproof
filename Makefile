FEATURES := yoloproofs

doc:
	cargo rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html

doc-internal:
	cargo rustdoc --features "$(FEATURES)" -- --html-in-header docs/assets/rustdoc-include-katex-header.html --document-private-items

