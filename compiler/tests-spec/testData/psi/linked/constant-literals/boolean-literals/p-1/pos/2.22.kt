/*
 * KOTLIN PSI SPEC TEST (POSITIVE)
 *
 * SPEC VERSION: 0.1-draft
 * PLACE: constant-literals, boolean-literals -> paragraph 1 -> sentence 2
 * NUMBER: 22
 * DESCRIPTION: The use of Boolean literals as the identifier (with backtick) in the labelDefinition.
 * NOTE: this test data is generated by FeatureInteractionTestDataGenerator. DO NOT MODIFY CODE MANUALLY!
 */

fun f() {
    val lambda_1 = `true`@ {}

    val lambda_2 = `false`@ {
        println(1)
    }

    val lambda_3 = @someAnotation `true`@ {
        println(1)
    }

    val lambda_4 = @someAnotation1 @someAnotation2 @someAnotation3 `false`@ {
        println(1)
    }

    val x1 = `true`@ 10 - 1
    val x2 = `false`@(listOf(1))
    val x3 = `true`@(return return) && `false`@ return return
    val x4 = `true`@ try {} finally {} && `false`@ return return
    val x5 = `true`@ try { false } catch(e: E) {} catch (e: Exception) { true } && `false`@ when (value) { `true`@ true -> `false`@ false; `true`@ false -> `false`@ true }
}
