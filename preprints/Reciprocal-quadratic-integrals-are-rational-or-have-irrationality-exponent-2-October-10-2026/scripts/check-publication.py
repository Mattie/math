"""Run the standalone package checks through the repository entry point."""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).with_name('check-package.py')), run_name='__main__')
