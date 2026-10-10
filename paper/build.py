"""Build the paper using pdflatex and bibtex already installed on PATH."""
from pathlib import Path
import argparse,shutil,subprocess,tempfile
parser=argparse.ArgumentParser()
parser.add_argument('--pdflatex',default='pdflatex')
parser.add_argument('--bibtex',default='bibtex')
args=parser.parse_args()
root=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='quantitative-paper-') as tmp:
 work=Path(tmp)
 for name in ['main.tex','refs.bib']:shutil.copyfile(root/name,work/name)
 shutil.copytree(root/'figures',work/'figures')
 latex=[args.pdflatex,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error','main.tex']
 for command in [latex,[args.bibtex,'main'],latex,latex]:
  result=subprocess.run(command,cwd=work,capture_output=True,text=True,timeout=180)
  if result.returncode:raise RuntimeError(result.stdout[-6000:]+result.stderr)
 log=(work/'main.log').read_text(errors='replace')
 import re
 assert not re.search(r'Overfull|undefined|multiply defined|^!',log,re.M),log[-8000:]
 for name in ['main.pdf','main.bbl']:shutil.copyfile(work/name,root/name)
 print('Built',root/'main.pdf')
