// Lean compiler output
// Module: Lean.Meta.RecExt
// Imports: public import Lean.Attributes
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "recExt"};
static const lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 192, 118, 202, 43, 9, 55, 48)}};
static const lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recExt;
static lean_once_cell_t l_Lean_Meta_markAsRecursive___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_markAsRecursive___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_markAsRecursive___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_));
v___x_8_ = ((lean_object*)(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_));
v___x_9_ = 0;
v___x_10_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2____boxed(lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
return v_res_12_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__0(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__1(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__0, &l_Lean_Meta_markAsRecursive___redArg___closed__0_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__0);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__2(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__1, &l_Lean_Meta_markAsRecursive___redArg___closed__1_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__1);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object* v_declName_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_env_22_; lean_object* v_nextMacroScope_23_; lean_object* v_ngen_24_; lean_object* v_auxDeclNGen_25_; lean_object* v_traceState_26_; lean_object* v_recordedDeps_27_; lean_object* v_messages_28_; lean_object* v_infoState_29_; lean_object* v_snapshotTasks_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_43_; 
v___x_21_ = lean_st_ref_take(v_a_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
v_nextMacroScope_23_ = lean_ctor_get(v___x_21_, 1);
v_ngen_24_ = lean_ctor_get(v___x_21_, 2);
v_auxDeclNGen_25_ = lean_ctor_get(v___x_21_, 3);
v_traceState_26_ = lean_ctor_get(v___x_21_, 4);
v_recordedDeps_27_ = lean_ctor_get(v___x_21_, 6);
v_messages_28_ = lean_ctor_get(v___x_21_, 7);
v_infoState_29_ = lean_ctor_get(v___x_21_, 8);
v_snapshotTasks_30_ = lean_ctor_get(v___x_21_, 9);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_21_, 5);
lean_dec(v_unused_44_);
v___x_32_ = v___x_21_;
v_isShared_33_ = v_isSharedCheck_43_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_snapshotTasks_30_);
lean_inc(v_infoState_29_);
lean_inc(v_messages_28_);
lean_inc(v_recordedDeps_27_);
lean_inc(v_traceState_26_);
lean_inc(v_auxDeclNGen_25_);
lean_inc(v_ngen_24_);
lean_inc(v_nextMacroScope_23_);
lean_inc(v_env_22_);
lean_dec(v___x_21_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_43_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_34_ = lean_box(0);
v___x_35_ = l_Lean_Meta_recExt;
v___x_36_ = l_Lean_TagDeclarationExtension_tag(v___x_35_, v_env_22_, v_declName_18_);
v___x_37_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__2, &l_Lean_Meta_markAsRecursive___redArg___closed__2_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__2);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 5, v___x_37_);
lean_ctor_set(v___x_32_, 0, v___x_36_);
v___x_39_ = v___x_32_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_nextMacroScope_23_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v_ngen_24_);
lean_ctor_set(v_reuseFailAlloc_42_, 3, v_auxDeclNGen_25_);
lean_ctor_set(v_reuseFailAlloc_42_, 4, v_traceState_26_);
lean_ctor_set(v_reuseFailAlloc_42_, 5, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_42_, 6, v_recordedDeps_27_);
lean_ctor_set(v_reuseFailAlloc_42_, 7, v_messages_28_);
lean_ctor_set(v_reuseFailAlloc_42_, 8, v_infoState_29_);
lean_ctor_set(v_reuseFailAlloc_42_, 9, v_snapshotTasks_30_);
v___x_39_ = v_reuseFailAlloc_42_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_st_ref_put(v_a_19_, v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_34_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object* v_declName_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_45_, v_a_46_);
lean_dec(v_a_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object* v_declName_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_49_, v_a_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object* v_declName_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_markAsRecursive(v_declName_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object* v_declName_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_toEnvExtension_65_; lean_object* v_asyncMode_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_62_ = lean_st_ref_get(v_a_60_);
v_env_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_env_63_);
lean_dec(v___x_62_);
v___x_64_ = l_Lean_Meta_recExt;
v_toEnvExtension_65_ = lean_ctor_get(v___x_64_, 0);
v_asyncMode_66_ = lean_ctor_get(v_toEnvExtension_65_, 2);
v___x_67_ = l_Lean_TagDeclarationExtension_isTagged(v___x_64_, v_env_63_, v_declName_59_, v_asyncMode_66_);
v___x_68_ = lean_box(v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object* v_declName_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_70_, v_a_71_);
lean_dec(v_a_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object* v_declName_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_74_, v_a_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object* v_declName_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_isRecursiveDefinition(v_declName_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
return v_res_83_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_RecExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_RecExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_RecExt(builtin);
}
#ifdef __cplusplus
}
#endif
