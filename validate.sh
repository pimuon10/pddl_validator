#!/bin/bash

./pddl <(tr A-Z a-z < $1) <(tr A-Z a-z < $2) <(tr A-Z a-z < $3)
