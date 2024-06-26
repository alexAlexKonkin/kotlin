// TARGET_BACKEND: JVM
// WITH_STDLIB

class Monitor

fun box(): String {
    val obj = Monitor() as java.lang.Object
    val e = IllegalArgumentException()
    fun m(): Nothing = throw e
    try {
        synchronized (m()) {
            throw AssertionError("Should not have reached this point")
        }
    }
    catch (caught: Throwable) {
        if (caught !== e) return "Fail: $caught"
    }

    return "OK"
}
