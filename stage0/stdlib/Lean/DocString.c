// Lean compiler output
// Module: Lean.DocString
// Imports: public import Lean.DocString.Extension public import Lean.DocString.Links public import Lean.Parser.Tactic.Doc public import Lean.Parser.Term.Doc
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object*, lean_object*);
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_rewriteManualLinks(lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object* v_env_1_, lean_object* v_declName_2_, uint8_t v_includeBuiltin_3_){
_start:
{
lean_object* v___y_6_; lean_object* v___x_30_; 
lean_inc(v_declName_2_);
lean_inc_ref(v_env_1_);
v___x_30_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_1_, v_declName_2_);
if (lean_obj_tag(v___x_30_) == 0)
{
v___y_6_ = v_declName_2_;
goto v___jp_5_;
}
else
{
lean_object* v_val_31_; 
lean_dec(v_declName_2_);
v_val_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_val_31_);
lean_dec_ref(v___x_30_);
v___y_6_ = v_val_31_;
goto v___jp_5_;
}
v___jp_5_:
{
lean_object* v_exts_7_; lean_object* v_spellings_8_; lean_object* v___x_9_; 
lean_inc_n(v___y_6_, 2);
lean_inc_ref_n(v_env_1_, 2);
v_exts_7_ = l_Lean_Parser_Tactic_Doc_getTacticExtensionString(v_env_1_, v___y_6_);
v_spellings_8_ = l_Lean_Parser_Term_Doc_getRecommendedSpellingString(v_env_1_, v___y_6_);
v___x_9_ = l_Lean_findSimpleDocString_x3f(v_env_1_, v___y_6_, v_includeBuiltin_3_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
if (lean_obj_tag(v_a_10_) == 0)
{
lean_dec_ref(v_spellings_8_);
lean_dec_ref(v_exts_7_);
return v___x_9_;
}
else
{
lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_28_; 
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v___x_9_, 0);
lean_dec(v_unused_29_);
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_28_;
goto v_resetjp_11_;
}
else
{
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_28_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v_val_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_27_; 
v_val_14_ = lean_ctor_get(v_a_10_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_27_ == 0)
{
v___x_16_ = v_a_10_;
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_val_14_);
lean_dec(v_a_10_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
v___x_18_ = lean_string_append(v_val_14_, v_exts_7_);
lean_dec_ref(v_exts_7_);
v___x_19_ = lean_string_append(v___x_18_, v_spellings_8_);
lean_dec_ref(v_spellings_8_);
v___x_20_ = l_Lean_rewriteManualLinks(v___x_19_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_20_);
v___x_22_ = v___x_16_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_24_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_22_);
v___x_24_ = v___x_12_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_spellings_8_);
lean_dec_ref(v_exts_7_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object* v_env_32_, lean_object* v_declName_33_, lean_object* v_includeBuiltin_34_, lean_object* v_a_35_){
_start:
{
uint8_t v_includeBuiltin_boxed_36_; lean_object* v_res_37_; 
v_includeBuiltin_boxed_36_ = lean_unbox(v_includeBuiltin_34_);
v_res_37_ = l_Lean_findDocString_x3f(v_env_32_, v_declName_33_, v_includeBuiltin_boxed_36_);
return v_res_37_;
}
}
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Doc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString(builtin);
}
#ifdef __cplusplus
}
#endif
