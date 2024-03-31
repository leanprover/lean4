#!/usr/bin/env bash
bash ./speedcenter-worker.sh 2>&1 | tee log.txt
temci report noreuse.speedcenter.bench.yaml reuse.speedcenter.bench.yaml > temci-report.txt
