# AGENTS.md

## Project

CCT is a dependency-free browser app for cognitive-control/PASAT training.

* `index.html` — UI
* `styles.css` — responsive light/dark styling
* `script.js` — application logic, persistence, audio, sessions, profiles, charts, and exports
* `audio/voices.js` — voice catalog
* `audio/<voice>/1.mp3` through `9.mp3` — audio assets

There is no framework, package manager, build process, backend, or external runtime dependency. Keep asset paths relative for GitHub Pages.

The app must work when opened directly with `file://` as well as when served over HTTP.

## Rules

* Preserve existing behavior unless the task explicitly changes it.
* Inspect relevant code before making non-trivial changes; prefer small, focused changes.
* Do not introduce dependencies or new tooling unless explicitly required.
* Preserve backward compatibility for existing localStorage/IndexedDB data and imported files.
* Keep keyboard accessibility, ARIA state, responsive layouts, and light/dark themes working.
* Preserve `audio/voices.js` before `script.js` in `index.html`.
* Do not overwrite or discard pre-existing user changes.

## Verification

* After JavaScript changes, run `node --check script.js` and `node --check audio/voices.js`.
* Open the app directly via `file://` and manually verify changed behavior. Use HTTP serving as needed to test behavior that requires it.
* For UI changes, check light/dark themes and a viewport at or below 700px.
* For session/data changes, verify affected persistence, history, profiles, and import/export behavior.
* Before finishing, run `git diff --check` and inspect `git diff`.
* There is currently no automated test or lint suite; do not claim that tests or lint passed.
