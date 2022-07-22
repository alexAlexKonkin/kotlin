/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package kotlin.js

private const val INT_SIZE = 32

internal class BitMask(vararg activeBits: Int) {
    private var intArray: IntArray

    init {
        val maxElement = activeBits.max()
        val countOfNumbers = maxElement.toDouble() / INT_SIZE.toDouble()
        val size = nativeCeil(countOfNumbers)
        intArray = IntArray(size)

        for (activeBit in activeBits) {
            val numberIndex = activeBit / INT_SIZE
            val positionInNumber = activeBit mod INT_SIZE
            val numberWithSettledBit = 1 shl positionInNumber
            intArray[numberIndex] = intArray[numberIndex] or numberWithSettledBit
        }
    }

    fun isBitSettled(possibleActiveBit: Int): Boolean {
        val numberIndex = possibleActiveBit / INT_SIZE
        if (numberIndex > intArray.size) return false
        val positionInNumber = possibleActiveBit mod INT_SIZE
        val numberWithSettledBit = 1 shl positionInNumber
        return intArray[numberIndex] and numberWithSettledBit != 0
    }

    private fun IntArray.max(): Int {
        var max = this[0]
        for (i in 1 until size) {
            val e = this[i]
            if (max < e) max = e
        }
        return max
    }

    @Suppress("UNUSED_PARAMETER")
    private fun nativeCeil(a: Double): Int {
        return js("Math.ceil(a)").unsafeCast<Int>()
    }

    @Suppress("UNUSED_PARAMETER", "UNUSED_VARIABLE")
    private infix fun Int.mod(other: Int): Int {
        val a = this
        return js("a % other").unsafeCast<Int>()
    }
}