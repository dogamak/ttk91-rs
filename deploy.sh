#!/bin/bash

INDEX_URL="https://raw.githubusercontent.com/rust-lang/crates.io-index/master"

# Prints messages to the standard error stream alongisde with the error level
# and name of the calling function. The error level can be set with the LEVEL
# environment variable and additional information with the PREFIX environment
# variable.
#
# Displays the first function name in FUNCNAME that does not begin with an
# underscore.
log() {
	if [[ -z "$LEVEL" ]]; then
		LEVEL=INFO
	fi

	if [[ "$LEVEL" == "ERR" ]]; then
		COLOR=$'\e[1;31m'
	fi

	COLOR_RESET=$'\e[0m'

	FUNC="$(tr ' ' $'\n'  <<< "${FUNCNAME[@]}" | grep -vE '^_' | tail -n+2 | head -n1)"
	printf '%s%-6s%s %s: %s%s\n' \
		"${COLOR}" \
		"[${LEVEL}]" \
		"${COLOR_RESET}" \
		"$FUNC" \
		"$PREFIX" \
		"$@" >&2
}

# Wrapper for commands that are likely to fail.  Captures the error stream of
# the specified command and prints it with log() if the command fails.
_fallible() {
	LOG_FILE="$(mktemp)"

	$@ 2> $LOG_FILE
	RESULT=$?

	if [[ $RESULT -ne 0 ]]; then
		LEVEL=ERR
		PREFIX="$1: "

		while read line; do
			log "$line"
		done < $LOG_FILE >&2

		exit 1
	fi

	rm $LOG_FILE
}

_curl() {
	log "Fetching $1"
	_fallible curl "$1"
}

_jq() {
	_fallible jq $@
}

fetch_published_versions() {
	CRATE_INDEX_PATH="$(sed 's_^\(..\)\(..\)_\1/\2/\0_' <<< $CRATE_NAME)"

	_curl "$INDEX_URL/$CRATE_INDEX_PATH" | _jq -r .vers
}

# Outputs value of the specified field of the package table in the Cargo manifest file.
get_manifest_field() {
	CARGO_TOML_PATH="$(cargo locate-project | _jq -r .root)"

	awk -f - "$CARGO_TOML_PATH" <<< '
		match($0, /^\[(.*)\]$/, ary) {
			table = ary[1]
		}

		match($0, /^\s*'$1'\s*=\s*"([^"]*)"/, ary) && table == "package" {
			print ary[1]
		}
	'
}

# Returns 0 if a new version of the crate should be published to crates.io.
publish_condition() {
	PUBLISHED_VERSIONS="$(fetch_published_versions)"
	LATEST_VERSION="$(tail -n1 <<< $PUBLISHED_VERSIONS)"

	log "Crate name:        $CRATE_NAME"
	log "Current version:   $CRATE_VERSION"
	log "Published version: $LATEST_VERSION"

	if grep -Fxq "$CRATE_VERSION" <<< "$PUBLISHED_VERSIONS"; then
		log "Current version has already been published"
		return 0
	else
		log "Current version has not yet been published"
		return 1
	fi
}

# Publishes the crate to crates.io
publish() {
	log "Configuring crates.io auth"
	_fallible cargo login "$CARGO_TOKEN"

	log "Publishing crate '$CRATE_NAME' version '$CRATE_VERSION' to crates.io"
	_fallible cargo publish 
}

CRATE_NAME="$(get_manifest_field name)"
CRATE_VERSION="$(get_manifest_field version)"

if [[ "$1" == "check" ]]; then
	publish_condition
	exit $?
elif [[ "$1" == "publish" ]]; then
	publish
elif [[ "$#" -eq "0" ]]; then
	publish_condition

	RESULT=$?
	if [[ $RESULT -eq 0 ]]; then
		publish
	fi
fi
