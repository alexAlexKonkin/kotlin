/*
 * KOTLIN PSI SPEC TEST (NEGATIVE)
 *
 * SPEC VERSION: 0.1-draft
 * PLACE: constant-literals, boolean-literals -> paragraph 1 -> sentence 2
 * NUMBER: 2
 * DESCRIPTION: The use of Boolean literals as the identifier (without backtick) in the labelReference.
 * NOTE: this test data is generated by FeatureInteractionTestDataGenerator. DO NOT MODIFY CODE MANUALLY!
 */

fun f() {
    return@true

    while (true) {
        break@false
        continue@true
    }
}
