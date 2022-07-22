/*
 * Copyright 2010-2022 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

// CHECK-NOT: call i32 @"kfun:kotlin#<Int-unbox>
// CHECK-NOT: invoke i32 @"kfun:kotlin#<Int-unbox>
// CHECK-NOT: call i32 @"kfun:kotlin#<UInt-unbox>
// CHECK-NOT: invoke i32 @"kfun:kotlin#<UInt-unbox>

// CHECK-NOT: call i64 @"kfun:kotlin#<Long-unbox>
// CHECK-NOT: invoke i64 @"kfun:kotlin#<Long-unbox>
// CHECK-NOT: call i64 @"kfun:kotlin#<ULong-unbox>
// CHECK-NOT: invoke i64 @"kfun:kotlin#<ULong-unbox>

// CHECK-NOT: call signext i16 @"kfun:kotlin#<Short-unbox>
// CHECK-NOT: invoke signext i16 @"kfun:kotlin#<Short-unbox>
// CHECK-NOT: call zeroext i16 @"kfun:kotlin#<UShort-unbox>
// CHECK-NOT: invoke zeroext i16 @"kfun:kotlin#<UShort-unbox>

// CHECK-NOT: call signext i8 @"kfun:kotlin#<Byte-unbox>
// CHECK-NOT: invoke signext i8 @"kfun:kotlin#<Byte-unbox>
// CHECK-NOT: call zeroext i8 @"kfun:kotlin#<UByte-unbox>
// CHECK-NOT: invoke zeroext i8 @"kfun:kotlin#<UByte-unbox>

// CHECK-NOT: call zeroext i16 @"kfun:kotlin#<Char-unbox>
// CHECK-NOT: invoke zeroext i16 @"kfun:kotlin#<Char-unbox>

// CHECK-NOT: call zeroext i1 @"kfun:kotlin#<Boolean-unbox>
// CHECK-NOT: invoke zeroext i1 @"kfun:kotlin#<Boolean-unbox>

// CHECK-NOT: call double @"kfun:kotlin#<Double-unbox>
// CHECK-NOT: invoke double @"kfun:kotlin#<Double-unbox>

// CHECK-NOT: call float @"kfun:kotlin#<Float-unbox>
// CHECK-NOT: invoke float @"kfun:kotlin#<Float-unbox>

// CHECK-NOT: call i8* @"kfun:kotlin.native.internal#<NativePtr-unbox>
// CHECK-NOT: invoke i8* @"kfun:kotlin.native.internal#<NativePtr-unbox>

// CHECK-NOT: call i32 @"kfun:kotlin.native.concurrent#<Future-unbox>
// CHECK-NOT: invoke i32 @"kfun:kotlin.native.concurrent#<Future-unbox>

// CHECK-NOT: call i32 @"kfun:kotlin.native.concurrent#<Worker-unbox>
// CHECK-NOT: invoke i32 @"kfun:kotlin.native.concurrent#<Worker-unbox>

// CHECK-NOT: call <4 x float> @"kfun:kotlin.native#<Vector128-unbox>
// CHECK-NOT: invoke <4 x float> @"kfun:kotlin.native#<Vector128-unbox>

// Generated functions IntToNSNumber and UIntToNSNumber may contain call to unbox functions
// CHECK-LABEL: IntToNSNumber
fun main(arr: Array<String>) {
    println(arr[0].toInt() + 1)
}
