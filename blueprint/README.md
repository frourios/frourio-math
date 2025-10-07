# Frourio Blueprint

This directory contains the blueprint documentation for the Frourio project.

## Building the blueprint

### Prerequisites

- Python 3.x
- LaTeX (for PDF generation)
- The `leanblueprint` Python package

### Installation

```bash
pip install leanblueprint
```

### Building

To build the PDF version:
```bash
cd blueprint
leanblueprint pdf
```

To build the web version:
```bash
cd blueprint
leanblueprint web
```

## Structure

- `src/content.tex` - Main content file
- `src/macros.tex` - LaTeX macros
- `src/print.tex` - Configuration for PDF output
- `src/web.tex` - Configuration for web output
- `lean_decls` - Mapping between blueprint labels and Lean declarations

## Editing

Edit the `src/content.tex` file to add or modify the blueprint content. Use standard LaTeX syntax for mathematical notation.
