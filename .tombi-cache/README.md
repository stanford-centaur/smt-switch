# Vendored JSON schemas

tombi validates TOML against schemas it bundles, but some of those refer out to
schemas it does not bundle and would otherwise fetch from schemastore on every
run. This directory holds copies of those, so CI validates against a fixed
version rather than whatever is served that day. See
[DEVELOPERS.md](../DEVELOPERS.md) for how CI is pointed here.

The layout is tombi's own cache layout, `https/<host>/<path>`, so each file has
to sit at the path its URL maps to. Every one is a download rather than a file
we maintain, so keep it byte-identical to upstream and let the pre-commit config
skip it.

## Refreshing

Nothing signals that a copy has gone stale, so re-download them now and then,
and after a tombi upgrade:

```sh
curl -o .tombi-cache/https/www.schemastore.org/partial-setuptools.json \
  https://www.schemastore.org/partial-setuptools.json
```

If that leaves a diff, run `pre-commit run --all-files` before committing it: a
schema change can start failing a file that used to pass.
