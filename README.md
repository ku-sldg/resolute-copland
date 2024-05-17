# Using This Template
1. Replace this readme with a description of the paper
2. Run `git submodules update --init` to get the latest `bib` file
3. Rename the file `samplepaper.tex` to something more meaningful
4. Replace `samplepaper` in the Makefile with your new paper name
5. Replace `samplepaper.pdf` in the `.gitignore` file so you don't end
   up checking in the built PDF file.
6. Edit the author section including emails, thanks, running header,
   and add orcid fields.	
7. Update the `bib` submodule and `sldg.bib` if needed by running
   `git submodule init` and `git submodule update`.
8. Descend into
   the `bib` directory and pull to get latest entries.  Push back to
   the lab repo if you add or edit entries.
9. Some includes are commented out as they are not always needed.
   Uncomment what you need and add others as needed. 
10. If you do not want to use `natbib` remove `\usepackage{natbib}`,
   add `\usepackage{cite}`, and swap `bibliographystyle` commands at
   the end of the document.
   
