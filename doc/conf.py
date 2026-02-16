# -*- coding: utf-8 -*-
#
# Configuration file for the Sphinx documentation builder.

import os
import sys

sys.path.insert(0, os.path.abspath('.'))
import fstar_pygments
from sphinx.highlighting import lexers

lexers['fstar'] = fstar_pygments.CustomLexer()
lexers['pulse'] = fstar_pygments.PulseLexer()

def setup(app):
    app.add_css_file('custom.css')

# -- Project information -----------------------------------------------------

project = u'Verified CLRS Algorithms in F* and Pulse'
copyright = u'2025, Nikhil Swamy and GitHub Copilot'
author = u'Nikhil Swamy and GitHub Copilot'

version = u'0.1'
release = u'0.1'

# -- General configuration ---------------------------------------------------

extensions = [
    'sphinx.ext.mathjax',
]

templates_path = ['_templates']
source_suffix = '.rst'
master_doc = 'index'
language = 'en'
exclude_patterns = [u'_build', 'Thumbs.db', '.DS_Store']
pygments_style = 'sphinx'

# -- Options for HTML output -------------------------------------------------

html_theme = 'sphinx_rtd_theme'
html_static_path = ['static']
html_show_sourcelink = False
htmlhelp_basename = 'AutoCLRSDoc'

# -- Options for LaTeX output ------------------------------------------------

latex_elements = {}
