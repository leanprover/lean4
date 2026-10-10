// Lean compiler output
// Module: Lean.Meta.PPBinder
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__0 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__0_value;
static lean_once_cell_t l_Lean_LocalDecl_ppAsBinder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_ppAsBinder___closed__1;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__2 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__2_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__3 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__3_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__4 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__4_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__5 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__5_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__6 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__6_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__7 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__7_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__8 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__8_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__9 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ppAsBinder(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_LocalDecl_ppAsBinder___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ppAsBinder(lean_object* v_x_12_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v_fvarId_13_; lean_object* v_type_14_; uint8_t v_bi_15_; lean_object* v_fst_17_; lean_object* v_snd_18_; 
v_fvarId_13_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_fvarId_13_);
v_type_14_ = lean_ctor_get(v_x_12_, 3);
lean_inc_ref(v_type_14_);
v_bi_15_ = lean_ctor_get_uint8(v_x_12_, sizeof(void*)*4);
lean_dec_ref_known(v_x_12_, 4);
switch(v_bi_15_)
{
case 0:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__2));
v___x_28_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__3));
v_fst_17_ = v___x_27_;
v_snd_18_ = v___x_28_;
goto v___jp_16_;
}
case 1:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__4));
v___x_30_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__5));
v_fst_17_ = v___x_29_;
v_snd_18_ = v___x_30_;
goto v___jp_16_;
}
case 2:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__6));
v___x_32_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__7));
v_fst_17_ = v___x_31_;
v_snd_18_ = v___x_32_;
goto v___jp_16_;
}
default: 
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__8));
v___x_34_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__9));
v_fst_17_ = v___x_33_;
v_snd_18_ = v___x_34_;
goto v___jp_16_;
}
}
v___jp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_19_ = l_Lean_mkFVar(v_fvarId_13_);
v___x_20_ = l_Lean_MessageData_ofExpr(v___x_19_);
v___x_21_ = lean_obj_once(&l_Lean_LocalDecl_ppAsBinder___closed__1, &l_Lean_LocalDecl_ppAsBinder___closed__1_once, _init_l_Lean_LocalDecl_ppAsBinder___closed__1);
v___x_22_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_20_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
v___x_23_ = l_Lean_MessageData_ofExpr(v_type_14_);
v___x_24_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
lean_inc_ref(v_snd_18_);
lean_inc_ref(v_fst_17_);
v___x_25_ = l_Lean_MessageData_bracket(v_fst_17_, v___x_24_, v_snd_18_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
else
{
lean_object* v___x_35_; 
lean_dec_ref_known(v_x_12_, 5);
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
}
lean_object* l_Lean_FVarId_ppAsBinder___redArg(lean_object* v_fvarId_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_50_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = l_Lean_LocalDecl_ppAsBinder(v_a_42_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_a_51_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_41_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_41_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_FVarId_ppAsBinder___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_36_ = stack[0].m_obj;
lean_object* v_a_37_ = stack[1].m_obj;
lean_object* v_a_38_ = stack[2].m_obj;
lean_object* v_a_39_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_FVarId_ppAsBinder___redArg(v_fvarId_36_, v_a_37_, v_a_38_, v_a_39_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg___boxed(lean_object* v_fvarId_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_FVarId_ppAsBinder___redArg(v_fvarId_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_65_;
}
}
lean_object* l_Lean_FVarId_ppAsBinder(lean_object* v_fvarId_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_66_, v_a_67_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = l_Lean_LocalDecl_ppAsBinder(v_a_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
v_a_82_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_72_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_72_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_FVarId_ppAsBinder_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_66_ = stack[0].m_obj;
lean_object* v_a_67_ = stack[1].m_obj;
lean_object* v_a_68_ = stack[2].m_obj;
lean_object* v_a_69_ = stack[3].m_obj;
lean_object* v_a_70_ = stack[4].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_FVarId_ppAsBinder(v_fvarId_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___boxed(lean_object* v_fvarId_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_FVarId_ppAsBinder(v_fvarId_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
return v_res_97_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_PPBinder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_PPBinder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_PPBinder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPBinder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_PPBinder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_PPBinder(builtin);
}
#ifdef __cplusplus
}
#endif
