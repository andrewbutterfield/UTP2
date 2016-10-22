#!/bin/bash
ls ../src/*.lhs > _lhs.log
ack -w import ../src/*.lhs > _import.log