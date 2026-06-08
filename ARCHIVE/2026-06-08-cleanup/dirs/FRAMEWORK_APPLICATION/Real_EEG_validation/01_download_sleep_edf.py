"""
01_download_sleep_edf.py
========================
Download a manageable subset of the PhysioNet Sleep-EDF Database.

Provenance:
  Source: https://physionet.org/content/sleep-edfx/1.0.0/
  Subset: Sleep Cassette, healthy subjects ages 25-101.
  Recording: PSG + hypnogram with sleep stages W, N1, N2, N3, REM scored
             per Rechtschaffen & Kales conventions on 30-s epochs.

We treat the binary "conscious vs unconscious" labels as follows
(neuro-physiologically standard):
  CONSCIOUS:   sleep stage W  (full wakefulness)
  UNCONSCIOUS: sleep stage N3 (slow-wave / deep NREM sleep -- the
              standard 'unresponsive' state used in consciousness research)

This mirrors the conscious/coma dichotomy used in the synthetic cohort.

We pull 10 subjects (1 recording each) which is ~50-100 MB of EDF files
and yields >>1000 30-s epochs per state per subject.
"""
import os, sys
from mne.datasets.sleep_physionet import age

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(HERE, 'raw_data')
os.makedirs(DATA_DIR, exist_ok=True)
os.environ['PHYSIONET_SLEEP_PATH'] = DATA_DIR

# Pull 10 healthy subjects, one night each.
SUBJECTS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
RECORDING = [1]

if __name__ == '__main__':
    print(f"Downloading Sleep-EDF for {len(SUBJECTS)} subjects to {DATA_DIR}")
    paths = age.fetch_data(subjects=SUBJECTS, recording=RECORDING,
                           path=DATA_DIR, on_missing='warn')
    print(f"\nDownloaded {len(paths)} subject(s):")
    for p in paths:
        # Each subject returns [PSG_edf, hypnogram_edf]
        for fp in p:
            sz = os.path.getsize(fp) / 1e6
            print(f"  {fp}  ({sz:.1f} MB)")
    print("\nDONE.")
