package com.empowerops.sojourn

fun trace(messageProvider: () -> String){
    System.err.println(messageProvider())
}