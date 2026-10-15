#!/usr/bin/env python3
"""Backward-compatible entry point for rebuilding all manuscript navigation."""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent / "rebuild_navigation.py"), run_name="__main__")
