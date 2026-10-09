"""Set the version 1.1 software release date after merge (UTC by default)."""
from pathlib import Path
import argparse
import datetime
import re


def checked_date(value):
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}', value):
        raise ValueError('FAIL: release date must be YYYY-MM-DD')
    date = datetime.date.fromisoformat(value)
    if date < datetime.date(2026, 10, 6):
        raise ValueError('FAIL: release date precedes arXiv v1')
    return date.isoformat()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--date', default=datetime.datetime.now(datetime.timezone.utc).date().isoformat())
    args = parser.parse_args()
    for invalid in ('2026-99-99', '2026-1-1', '2026-10-05'):
        try:
            checked_date(invalid)
        except ValueError:
            pass
        else:
            raise ValueError('FAIL: invalid-date control accepted')
    value = checked_date(args.date)
    citation = Path(__file__).resolve().parent.parent/'CITATION.cff'
    text = citation.read_text()
    if 'version: "1.1"\n' not in text:
        raise ValueError('FAIL: software version is not 1.1')
    if re.search(r'^date-released:', text, re.M):
        existing = re.search(r'^date-released:\s*(\S+)\s*$', text, re.M)
        if existing is None or existing[1] != value:
            raise ValueError('FAIL: an existing release date must be preserved')
    else:
        text = text.replace('version: "1.1"\n', 'version: "1.1"\ndate-released: '+value+'\n', 1)
        citation.write_text(text)
    print('PASS: software release date set to '+value)


if __name__ == '__main__':
    try:
        main()
    except ValueError as error:
        raise SystemExit(str(error)) from None
