typealias Callback = () -> Unit

class CallbackComposer {
    inline fun addTo(noinline block: Callback) {
        asDynamic().push(block)
    }
}

fun createCallbackBuilder(builder: CallbackComposer.() -> Unit): () -> Callback = {
    val callbacks = arrayOf<Callback>()
    builder(callbacks.unsafeCast<CallbackComposer>())

    val composed: Callback = {
        for (cb in callbacks) {
            cb()
        }
    }
    composed
}

var retVal = "Fail"

fun setRetValToOk(): () -> Unit = {
    retVal = "OK"
}



fun box(): String {
    val callbackBuilder = createCallbackBuilder {
        setRetValToOk().also(::addTo)
    }

    val callback = callbackBuilder()
    callback()

    return retVal
}
