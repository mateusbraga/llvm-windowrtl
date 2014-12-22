#include <stdio.h>
#include <sanitizer/dfsan_interface.h>

dfsan_label globalInputLabel;

void dfrtl_check(const void* addr, size_t size) {
    printf("WindowRtl: Is addr %p size %zu tainted? ", addr, size);
    dfsan_label value_label = dfsan_read_label(addr, size);
    if(dfsan_has_label(value_label, globalInputLabel)) {
        printf("yes\n");
    } else {
        printf("no\n");
    }
}

void dfrtl_add_input_label(void* addr, size_t size) {
    if (globalInputLabel == 0) {
        printf("WindowRtl: Created global input label\n");
        globalInputLabel = dfsan_create_label("input", 0);
    }
    dfsan_set_label(globalInputLabel, addr, size);
    printf("WindowRtl: Tainted %p size %zd\n", addr, size);
}
