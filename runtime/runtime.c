#include <stdio.h>
#include <sanitizer/dfsan_interface.h>

dfsan_label globalInputLabel;

void dfrtl_check(int value) {
    printf("WindowRtl: Checking if value %d is tainted: ", value);
    dfsan_label value_label = dfsan_get_label(value);
    if(dfsan_has_label(value_label, globalInputLabel)) {
        printf("yes\n");
    } else {
        printf("no\n");
    }
}

void dfrtl_add_input_label(void* input_to_taint, unsigned long size) {
    if (globalInputLabel == 0) {
        printf("WindowRtl: Created global input label\n");
        globalInputLabel = dfsan_create_label("input", 0);
    }
    dfsan_set_label(globalInputLabel, input_to_taint, size);
    printf("WindowRtl: Tainted %p size %zd\n", input_to_taint, size);
    int* conv = (int*) input_to_taint;
    /*printf("Value of input %d\n", *conv);*/
    /*dfsan_label value_label = dfsan_get_label(*conv);*/
    /*if(dfsan_has_label(value_label, globalInputLabel)) {*/
        /*printf("in dfrtl_add_input_label %d is tainted by input\n", *conv);*/
    /*}*/
    // this call seems to make everything work.
    
    printf("WindowRtl: Bootstrap call: ");
    dfrtl_check(*conv);
}
