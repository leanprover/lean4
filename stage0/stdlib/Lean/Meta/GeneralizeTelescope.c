// Lean compiler output
// Module: Lean.Meta.GeneralizeTelescope
// Imports: public import Lean.Meta.KAbstract public import Lean.Meta.Check
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to create telescope generalizing "};
static const lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_generalizeTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_generalizeTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_generalizeTelescope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object* v_e_1_, lean_object* v_eNew_2_, lean_object* v_entries_3_, lean_object* v_i_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_array_get_size(v_entries_3_);
v___x_11_ = lean_nat_dec_lt(v_i_4_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
lean_dec(v_i_4_);
lean_dec_ref(v_e_1_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v_entries_3_);
return v___x_12_;
}
else
{
lean_object* v_entry_13_; lean_object* v_expr_14_; lean_object* v_type_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_42_; 
v_entry_13_ = lean_array_fget(v_entries_3_, v_i_4_);
v_expr_14_ = lean_ctor_get(v_entry_13_, 0);
v_type_15_ = lean_ctor_get(v_entry_13_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_entry_13_);
if (v_isSharedCheck_42_ == 0)
{
v___x_17_ = v_entry_13_;
v_isShared_18_ = v_isSharedCheck_42_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_type_15_);
lean_inc(v_expr_14_);
lean_dec(v_entry_13_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_42_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_box(0);
lean_inc_ref(v_e_1_);
v___x_20_ = l_Lean_Meta_kabstract(v_type_15_, v_e_1_, v___x_19_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; uint8_t v___x_22_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_20_, 1);
v___x_22_ = l_Lean_Expr_hasLooseBVars(v_a_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_a_21_);
lean_del_object(v___x_17_);
lean_dec_ref(v_expr_14_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_i_4_, v___x_23_);
lean_dec(v_i_4_);
v_i_4_ = v___x_24_;
goto _start;
}
else
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = lean_expr_instantiate1(v_a_21_, v_eNew_2_);
lean_dec(v_a_21_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_26_);
v___x_28_ = v___x_17_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_expr_14_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_26_);
v___x_28_ = v_reuseFailAlloc_33_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*2, v___x_11_);
v___x_29_ = lean_array_fset(v_entries_3_, v_i_4_, v___x_28_);
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = lean_nat_add(v_i_4_, v___x_30_);
lean_dec(v_i_4_);
v_entries_3_ = v___x_29_;
v_i_4_ = v___x_31_;
goto _start;
}
}
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_del_object(v___x_17_);
lean_dec_ref(v_expr_14_);
lean_dec(v_i_4_);
lean_dec_ref(v_entries_3_);
lean_dec_ref(v_e_1_);
v_a_34_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_20_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_20_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_GeneralizeTelescope_updateTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_eNew_2_ = stack[1].m_obj;
lean_object* v_entries_3_ = stack[2].m_obj;
lean_object* v_i_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(v_e_1_, v_eNew_2_, v_entries_3_, v_i_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object* v_e_44_, lean_object* v_eNew_45_, lean_object* v_entries_46_, lean_object* v_i_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(v_e_44_, v_eNew_45_, v_entries_46_, v_i_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec_ref(v_eNew_45_);
return v_res_53_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(lean_object* v_msgData_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_env_61_; uint8_t v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_toCold_65_; lean_object* v_mctx_66_; lean_object* v_lctx_67_; lean_object* v_options_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_60_ = lean_st_ref_get(v___y_58_);
v_env_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_env_61_);
lean_dec(v___x_60_);
v___x_62_ = 0;
v_env_63_ = l_Lean_Environment_setRecordingDeps(v_env_61_, v___x_62_);
v___x_64_ = lean_st_ref_get(v___y_56_);
v_toCold_65_ = lean_ctor_get(v___y_57_, 0);
v_mctx_66_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_mctx_66_);
lean_dec(v___x_64_);
v_lctx_67_ = lean_ctor_get(v___y_55_, 2);
v_options_68_ = lean_ctor_get(v_toCold_65_, 2);
lean_inc_ref(v_options_68_);
lean_inc_ref(v_lctx_67_);
v___x_69_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_69_, 0, v_env_63_);
lean_ctor_set(v___x_69_, 1, v_mctx_66_);
lean_ctor_set(v___x_69_, 2, v_lctx_67_);
lean_ctor_set(v___x_69_, 3, v_options_68_);
v___x_70_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_msgData_54_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_54_ = stack[0].m_obj;
lean_object* v___y_55_ = stack[1].m_obj;
lean_object* v___y_56_ = stack[2].m_obj;
lean_object* v___y_57_ = stack[3].m_obj;
lean_object* v___y_58_ = stack[4].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msgData_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4___boxed(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msgData_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_79_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_ref_86_; lean_object* v___x_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_ref_86_ = lean_ctor_get(v___y_83_, 2);
v___x_87_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_inc(v_ref_86_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_ref_86_);
lean_ctor_set(v___x_92_, 1, v_a_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_80_ = stack[0].m_obj;
lean_object* v___y_81_ = stack[1].m_obj;
lean_object* v___y_82_ = stack[2].m_obj;
lean_object* v___y_83_ = stack[3].m_obj;
lean_object* v___y_84_ = stack[4].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg___boxed(lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(lean_object* v_k_105_, lean_object* v_b_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
v___x_112_ = lean_apply_6(v_k_105_, v_b_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, lean_box(0));
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_105_ = stack[0].m_obj;
lean_object* v_b_106_ = stack[1].m_obj;
lean_object* v___y_107_ = stack[2].m_obj;
lean_object* v___y_108_ = stack[3].m_obj;
lean_object* v___y_109_ = stack[4].m_obj;
lean_object* v___y_110_ = stack[5].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(v_k_105_, v_b_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_114_, lean_object* v_b_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(v_k_114_, v_b_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(lean_object* v_name_122_, uint8_t v_bi_123_, lean_object* v_type_124_, lean_object* v_k_125_, uint8_t v_kind_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___f_132_; lean_object* v___x_133_; 
v___f_132_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_132_, 0, v_k_125_);
v___x_133_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_122_, v_bi_123_, v_type_124_, v___f_132_, v_kind_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_133_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_133_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_122_ = stack[0].m_obj;
uint8_t v_bi_123_ = stack[1].m_num;
lean_object* v_type_124_ = stack[2].m_obj;
lean_object* v_k_125_ = stack[3].m_obj;
uint8_t v_kind_126_ = stack[4].m_num;
lean_object* v___y_127_ = stack[5].m_obj;
lean_object* v___y_128_ = stack[6].m_obj;
lean_object* v___y_129_ = stack[7].m_obj;
lean_object* v___y_130_ = stack[8].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_122_, v_bi_123_, v_type_124_, v_k_125_, v_kind_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___boxed(lean_object* v_name_151_, lean_object* v_bi_152_, lean_object* v_type_153_, lean_object* v_k_154_, lean_object* v_kind_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
uint8_t v_bi_boxed_161_; uint8_t v_kind_boxed_162_; lean_object* v_res_163_; 
v_bi_boxed_161_ = lean_unbox(v_bi_152_);
v_kind_boxed_162_ = lean_unbox(v_kind_155_);
v_res_163_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_151_, v_bi_boxed_161_, v_type_153_, v_k_154_, v_kind_boxed_162_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_163_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(lean_object* v_name_164_, lean_object* v_type_165_, lean_object* v_k_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
uint8_t v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; 
v___x_172_ = 0;
v___x_173_ = 0;
v___x_174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_164_, v___x_172_, v_type_165_, v_k_166_, v___x_173_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_164_ = stack[0].m_obj;
lean_object* v_type_165_ = stack[1].m_obj;
lean_object* v_k_166_ = stack[2].m_obj;
lean_object* v___y_167_ = stack[3].m_obj;
lean_object* v___y_168_ = stack[4].m_obj;
lean_object* v___y_169_ = stack[5].m_obj;
lean_object* v___y_170_ = stack[6].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_164_, v_type_165_, v_k_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg___boxed(lean_object* v_name_176_, lean_object* v_type_177_, lean_object* v_k_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_176_, v_type_177_, v_k_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
if (lean_obj_tag(v_a_185_) == 0)
{
lean_object* v___x_187_; 
v___x_187_ = l_List_reverse___redArg(v_a_186_);
return v___x_187_;
}
else
{
lean_object* v_head_188_; lean_object* v_tail_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_198_; 
v_head_188_ = lean_ctor_get(v_a_185_, 0);
v_tail_189_ = lean_ctor_get(v_a_185_, 1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_198_ == 0)
{
v___x_191_ = v_a_185_;
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_tail_189_);
lean_inc(v_head_188_);
lean_dec(v_a_185_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_MessageData_ofExpr(v_head_188_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v_a_186_);
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_a_186_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v_a_185_ = v_tail_189_;
v_a_186_ = v___x_195_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(size_t v_sz_199_, size_t v_i_200_, lean_object* v_bs_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_lt(v_i_200_, v_sz_199_);
if (v___x_202_ == 0)
{
return v_bs_201_;
}
else
{
lean_object* v_v_203_; lean_object* v_expr_204_; lean_object* v___x_205_; lean_object* v_bs_x27_206_; size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v_v_203_ = lean_array_uget_borrowed(v_bs_201_, v_i_200_);
v_expr_204_ = lean_ctor_get(v_v_203_, 0);
lean_inc_ref(v_expr_204_);
v___x_205_ = lean_unsigned_to_nat(0u);
v_bs_x27_206_ = lean_array_uset(v_bs_201_, v_i_200_, v___x_205_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_add(v_i_200_, v___x_207_);
v___x_209_ = lean_array_uset(v_bs_x27_206_, v_i_200_, v_expr_204_);
v_i_200_ = v___x_208_;
v_bs_201_ = v___x_209_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_199_ = stack[0].m_num;
size_t v_i_200_ = stack[1].m_num;
lean_object* v_bs_201_ = stack[2].m_obj;
lean_object* v_res_211_;
v_res_211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_199_, v_i_200_, v_bs_201_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1___boxed(lean_object* v_sz_212_, lean_object* v_i_213_, lean_object* v_bs_214_){
_start:
{
size_t v_sz_boxed_215_; size_t v_i_boxed_216_; lean_object* v_res_217_; 
v_sz_boxed_215_ = lean_unbox_usize(v_sz_212_);
lean_dec(v_sz_212_);
v_i_boxed_216_ = lean_unbox_usize(v_i_213_);
lean_dec(v_i_213_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_boxed_215_, v_i_boxed_216_, v_bs_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed(lean_object* v_i_218_, lean_object* v_e_219_, lean_object* v_entries_220_, lean_object* v_fvars_221_, lean_object* v_k_222_, lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(v_i_218_, v_e_219_, v_entries_220_, v_fvars_221_, v_k_222_, v_x_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v_i_218_);
return v_res_229_;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(lean_object* v_k_236_, lean_object* v_entries_237_, lean_object* v_i_238_, lean_object* v_fvars_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_baseUserName_246_; lean_object* v_e_247_; lean_object* v_type_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_array_get_size(v_entries_237_);
v___x_274_ = lean_nat_dec_lt(v_i_238_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v_i_238_);
lean_dec_ref(v_entries_237_);
lean_inc(v_a_243_);
lean_inc_ref(v_a_242_);
lean_inc(v_a_241_);
lean_inc_ref(v_a_240_);
v___x_275_ = lean_apply_6(v_k_236_, v_fvars_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, lean_box(0));
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v_expr_277_; lean_object* v_type_278_; uint8_t v_modified_279_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; 
v___x_276_ = lean_array_fget_borrowed(v_entries_237_, v_i_238_);
v_expr_277_ = lean_ctor_get(v___x_276_, 0);
v_type_278_ = lean_ctor_get(v___x_276_, 1);
v_modified_279_ = lean_ctor_get_uint8(v___x_276_, sizeof(void*)*2);
if (lean_obj_tag(v_expr_277_) == 1)
{
if (v_modified_279_ == 0)
{
lean_object* v_fvarId_314_; lean_object* v___x_315_; 
v_fvarId_314_ = lean_ctor_get(v_expr_277_, 0);
lean_inc(v_fvarId_314_);
v___x_315_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_314_, v_a_240_, v_a_242_, v_a_243_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
if (lean_obj_tag(v_a_316_) == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref_known(v_a_316_, 4);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_add(v_i_238_, v___x_317_);
lean_dec(v_i_238_);
lean_inc_ref(v_expr_277_);
v___x_319_ = lean_array_push(v_fvars_239_, v_expr_277_);
v_i_238_ = v___x_318_;
v_fvars_239_ = v___x_319_;
goto _start;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_LocalDecl_userName(v_a_316_);
lean_dec_ref_known(v_a_316_, 5);
lean_inc_ref(v_type_278_);
lean_inc_ref(v_expr_277_);
v_baseUserName_246_ = v___x_321_;
v_e_247_ = v_expr_277_;
v_type_248_ = v_type_278_;
v___y_249_ = v_a_240_;
v___y_250_ = v_a_241_;
v___y_251_ = v_a_242_;
v___y_252_ = v_a_243_;
goto v___jp_245_;
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v_fvars_239_);
lean_dec(v_i_238_);
lean_dec_ref(v_entries_237_);
lean_dec_ref(v_k_236_);
v_a_322_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_315_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_315_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
v___y_281_ = v_a_240_;
v___y_282_ = v_a_241_;
v___y_283_ = v_a_242_;
v___y_284_ = v_a_243_;
goto v___jp_280_;
}
}
else
{
v___y_281_ = v_a_240_;
v___y_282_ = v_a_241_;
v___y_283_ = v_a_242_;
v___y_284_ = v_a_243_;
goto v___jp_280_;
}
v___jp_280_:
{
if (v_modified_279_ == 0)
{
lean_inc_ref(v_type_278_);
lean_inc_ref(v_expr_277_);
v___y_266_ = v_expr_277_;
v___y_267_ = v_type_278_;
v___y_268_ = v___y_281_;
v___y_269_ = v___y_282_;
v___y_270_ = v___y_283_;
v___y_271_ = v___y_284_;
goto v___jp_265_;
}
else
{
lean_object* v___x_285_; 
lean_inc_ref(v_type_278_);
v___x_285_ = l_Lean_Meta_isTypeCorrect(v_type_278_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; uint8_t v___x_287_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = lean_unbox(v_a_286_);
lean_dec(v_a_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; size_t v_sz_289_; size_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_288_ = lean_obj_once(&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3, &l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once, _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3);
v_sz_289_ = lean_array_size(v_entries_237_);
v___x_290_ = ((size_t)0ULL);
lean_inc_ref(v_entries_237_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_289_, v___x_290_, v_entries_237_);
v___x_292_ = lean_array_to_list(v___x_291_);
v___x_293_ = lean_box(0);
v___x_294_ = l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(v___x_292_, v___x_293_);
v___x_295_ = l_Lean_MessageData_ofList(v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_288_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v___x_296_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_dec_ref_known(v___x_297_, 1);
lean_inc_ref(v_type_278_);
lean_inc_ref(v_expr_277_);
v___y_266_ = v_expr_277_;
v___y_267_ = v_type_278_;
v___y_268_ = v___y_281_;
v___y_269_ = v___y_282_;
v___y_270_ = v___y_283_;
v___y_271_ = v___y_284_;
goto v___jp_265_;
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_fvars_239_);
lean_dec(v_i_238_);
lean_dec_ref(v_entries_237_);
lean_dec_ref(v_k_236_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_inc_ref(v_type_278_);
lean_inc_ref(v_expr_277_);
v___y_266_ = v_expr_277_;
v___y_267_ = v_type_278_;
v___y_268_ = v___y_281_;
v___y_269_ = v___y_282_;
v___y_270_ = v___y_283_;
v___y_271_ = v___y_284_;
goto v___jp_265_;
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref(v_fvars_239_);
lean_dec(v_i_238_);
lean_dec_ref(v_entries_237_);
lean_dec_ref(v_k_236_);
v_a_306_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_285_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_285_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
v___jp_245_:
{
lean_object* v___f_253_; lean_object* v___x_254_; 
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_253_, 0, v_i_238_);
lean_closure_set(v___f_253_, 1, v_e_247_);
lean_closure_set(v___f_253_, 2, v_entries_237_);
lean_closure_set(v___f_253_, 3, v_fvars_239_);
lean_closure_set(v___f_253_, 4, v_k_236_);
v___x_254_ = l_Lean_Core_mkFreshUserName(v_baseUserName_246_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_a_255_, v_type_248_, v___f_253_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_256_;
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec_ref(v___f_253_);
lean_dec_ref(v_type_248_);
v_a_257_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_254_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
v___jp_265_:
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1));
v_baseUserName_246_ = v___x_272_;
v_e_247_ = v___y_266_;
v_type_248_ = v___y_267_;
v___y_249_ = v___y_268_;
v___y_250_ = v___y_269_;
v___y_251_ = v___y_270_;
v___y_252_ = v___y_271_;
goto v___jp_245_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_236_ = stack[0].m_obj;
lean_object* v_entries_237_ = stack[1].m_obj;
lean_object* v_i_238_ = stack[2].m_obj;
lean_object* v_fvars_239_ = stack[3].m_obj;
lean_object* v_a_240_ = stack[4].m_obj;
lean_object* v_a_241_ = stack[5].m_obj;
lean_object* v_a_242_ = stack[6].m_obj;
lean_object* v_a_243_ = stack[7].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_236_, v_entries_237_, v_i_238_, v_fvars_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
stack->m_obj
 = v_res_330_;
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(lean_object* v_i_331_, lean_object* v_e_332_, lean_object* v_entries_333_, lean_object* v_fvars_334_, lean_object* v_k_335_, lean_object* v_x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_331_, v___x_342_);
lean_inc(v___x_343_);
v___x_344_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(v_e_332_, v_x_336_, v_entries_333_, v___x_343_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = lean_array_push(v_fvars_334_, v_x_336_);
v___x_347_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_335_, v_a_345_, v___x_343_, v___x_346_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v___x_343_);
lean_dec_ref(v_x_336_);
lean_dec_ref(v_k_335_);
lean_dec_ref(v_fvars_334_);
v_a_348_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_344_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_344_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_331_ = stack[0].m_obj;
lean_object* v_e_332_ = stack[1].m_obj;
lean_object* v_entries_333_ = stack[2].m_obj;
lean_object* v_fvars_334_ = stack[3].m_obj;
lean_object* v_k_335_ = stack[4].m_obj;
lean_object* v_x_336_ = stack[5].m_obj;
lean_object* v___y_337_ = stack[6].m_obj;
lean_object* v___y_338_ = stack[7].m_obj;
lean_object* v___y_339_ = stack[8].m_obj;
lean_object* v___y_340_ = stack[9].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(v_i_331_, v_e_332_, v_entries_333_, v_fvars_334_, v_k_335_, v_x_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___boxed(lean_object* v_k_357_, lean_object* v_entries_358_, lean_object* v_i_359_, lean_object* v_fvars_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_357_, v_entries_358_, v_i_359_, v_fvars_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
return v_res_366_;
}
}
lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object* v_00_u03b1_367_, lean_object* v_k_368_, lean_object* v_entries_369_, lean_object* v_i_370_, lean_object* v_fvars_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_368_, v_entries_369_, v_i_370_, v_fvars_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_368_ = stack[1].m_obj;
lean_object* v_entries_369_ = stack[2].m_obj;
lean_object* v_i_370_ = stack[3].m_obj;
lean_object* v_fvars_371_ = stack[4].m_obj;
lean_object* v_a_372_ = stack[5].m_obj;
lean_object* v_a_373_ = stack[6].m_obj;
lean_object* v_a_374_ = stack[7].m_obj;
lean_object* v_a_375_ = stack[8].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_box(0), v_k_368_, v_entries_369_, v_i_370_, v_fvars_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___boxed(lean_object* v_00_u03b1_379_, lean_object* v_k_380_, lean_object* v_entries_381_, lean_object* v_i_382_, lean_object* v_fvars_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(v_00_u03b1_379_, v_k_380_, v_entries_381_, v_i_382_, v_fvars_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_389_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(lean_object* v_00_u03b1_390_, lean_object* v_name_391_, uint8_t v_bi_392_, lean_object* v_type_393_, lean_object* v_k_394_, uint8_t v_kind_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_391_, v_bi_392_, v_type_393_, v_k_394_, v_kind_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_391_ = stack[1].m_obj;
uint8_t v_bi_392_ = stack[2].m_num;
lean_object* v_type_393_ = stack[3].m_obj;
lean_object* v_k_394_ = stack[4].m_obj;
uint8_t v_kind_395_ = stack[5].m_num;
lean_object* v___y_396_ = stack[6].m_obj;
lean_object* v___y_397_ = stack[7].m_obj;
lean_object* v___y_398_ = stack[8].m_obj;
lean_object* v___y_399_ = stack[9].m_obj;
lean_object* v_res_402_;
v_res_402_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(lean_box(0), v_name_391_, v_bi_392_, v_type_393_, v_k_394_, v_kind_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___boxed(lean_object* v_00_u03b1_403_, lean_object* v_name_404_, lean_object* v_bi_405_, lean_object* v_type_406_, lean_object* v_k_407_, lean_object* v_kind_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
uint8_t v_bi_boxed_414_; uint8_t v_kind_boxed_415_; lean_object* v_res_416_; 
v_bi_boxed_414_ = lean_unbox(v_bi_405_);
v_kind_boxed_415_ = lean_unbox(v_kind_408_);
v_res_416_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(v_00_u03b1_403_, v_name_404_, v_bi_boxed_414_, v_type_406_, v_k_407_, v_kind_boxed_415_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_416_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(lean_object* v_00_u03b1_417_, lean_object* v_name_418_, lean_object* v_type_419_, lean_object* v_k_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_418_, v_type_419_, v_k_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
return v___x_426_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_418_ = stack[1].m_obj;
lean_object* v_type_419_ = stack[2].m_obj;
lean_object* v_k_420_ = stack[3].m_obj;
lean_object* v___y_421_ = stack[4].m_obj;
lean_object* v___y_422_ = stack[5].m_obj;
lean_object* v___y_423_ = stack[6].m_obj;
lean_object* v___y_424_ = stack[7].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(lean_box(0), v_name_418_, v_type_419_, v_k_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___boxed(lean_object* v_00_u03b1_428_, lean_object* v_name_429_, lean_object* v_type_430_, lean_object* v_k_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(v_00_u03b1_428_, v_name_429_, v_type_430_, v_k_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(lean_object* v_00_u03b1_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_439_ = stack[1].m_obj;
lean_object* v___y_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(lean_box(0), v_msg_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___boxed(lean_object* v_00_u03b1_447_, lean_object* v_msg_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(v_00_u03b1_447_, v_msg_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_454_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(lean_object* v_e_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = l_Lean_Expr_hasMVar(v_e_455_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_e_455_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v_mctx_461_; lean_object* v___x_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_465_; lean_object* v_cache_466_; lean_object* v_zetaDeltaFVarIds_467_; lean_object* v_postponed_468_; lean_object* v_diag_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_478_; 
v___x_460_ = lean_st_ref_get(v___y_456_);
v_mctx_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_ref(v_mctx_461_);
lean_dec(v___x_460_);
v___x_462_ = l_Lean_instantiateMVarsCore(v_mctx_461_, v_e_455_);
v_fst_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_fst_463_);
v_snd_464_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_snd_464_);
lean_dec_ref(v___x_462_);
v___x_465_ = lean_st_ref_take(v___y_456_);
v_cache_466_ = lean_ctor_get(v___x_465_, 1);
v_zetaDeltaFVarIds_467_ = lean_ctor_get(v___x_465_, 2);
v_postponed_468_ = lean_ctor_get(v___x_465_, 3);
v_diag_469_ = lean_ctor_get(v___x_465_, 4);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___x_465_, 0);
lean_dec(v_unused_479_);
v___x_471_ = v___x_465_;
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_diag_469_);
lean_inc(v_postponed_468_);
lean_inc(v_zetaDeltaFVarIds_467_);
lean_inc(v_cache_466_);
lean_dec(v___x_465_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v_snd_464_);
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_snd_464_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_cache_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_zetaDeltaFVarIds_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_postponed_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_diag_469_);
v___x_474_ = v_reuseFailAlloc_477_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_st_ref_put(v___y_456_, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_fst_463_);
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_455_ = stack[0].m_obj;
lean_object* v___y_456_ = stack[1].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_455_, v___y_456_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg___boxed(lean_object* v_e_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_481_, v___y_482_);
lean_dec(v___y_482_);
return v_res_484_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(lean_object* v_e_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_485_, v___y_487_);
return v___x_491_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_485_ = stack[0].m_obj;
lean_object* v___y_486_ = stack[1].m_obj;
lean_object* v___y_487_ = stack[2].m_obj;
lean_object* v___y_488_ = stack[3].m_obj;
lean_object* v___y_489_ = stack[4].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(v_e_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___boxed(lean_object* v_e_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(v_e_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_499_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(size_t v_sz_500_, size_t v_i_501_, lean_object* v_bs_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_501_, v_sz_500_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_bs_502_);
return v___x_509_;
}
else
{
lean_object* v_v_510_; lean_object* v___x_511_; lean_object* v_bs_x27_512_; lean_object* v___x_513_; 
v_v_510_ = lean_array_uget(v_bs_502_, v_i_501_);
v___x_511_ = lean_unsigned_to_nat(0u);
v_bs_x27_512_ = lean_array_uset(v_bs_502_, v_i_501_, v___x_511_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v_v_510_);
v___x_513_ = lean_infer_type(v_v_510_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_a_514_, v___y_504_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; uint8_t v___x_517_; lean_object* v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = 0;
v___x_518_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_518_, 0, v_v_510_);
lean_ctor_set(v___x_518_, 1, v_a_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*2, v___x_517_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_501_, v___x_519_);
v___x_521_ = lean_array_uset(v_bs_x27_512_, v_i_501_, v___x_518_);
v_i_501_ = v___x_520_;
v_bs_502_ = v___x_521_;
goto _start;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_bs_x27_512_);
lean_dec(v_v_510_);
v_a_523_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_515_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_515_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_bs_x27_512_);
lean_dec(v_v_510_);
v_a_531_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_513_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_513_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_500_ = stack[0].m_num;
size_t v_i_501_ = stack[1].m_num;
lean_object* v_bs_502_ = stack[2].m_obj;
lean_object* v___y_503_ = stack[3].m_obj;
lean_object* v___y_504_ = stack[4].m_obj;
lean_object* v___y_505_ = stack[5].m_obj;
lean_object* v___y_506_ = stack[6].m_obj;
lean_object* v_res_539_;
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_500_, v_i_501_, v_bs_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1___boxed(lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
size_t v_sz_boxed_548_; size_t v_i_boxed_549_; lean_object* v_res_550_; 
v_sz_boxed_548_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_549_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_boxed_548_, v_i_boxed_549_, v_bs_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_550_;
}
}
lean_object* l_Lean_Meta_generalizeTelescope___redArg(lean_object* v_es_553_, lean_object* v_k_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
size_t v_sz_560_; size_t v___x_561_; lean_object* v___x_562_; 
v_sz_560_ = lean_array_size(v_es_553_);
v___x_561_ = ((size_t)0ULL);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_560_, v___x_561_, v_es_553_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = ((lean_object*)(l_Lean_Meta_generalizeTelescope___redArg___closed__0));
v___x_566_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_554_, v_a_563_, v___x_564_, v___x_565_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
return v___x_566_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_k_554_);
v_a_567_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_562_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_562_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeTelescope___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_553_ = stack[0].m_obj;
lean_object* v_k_554_ = stack[1].m_obj;
lean_object* v_a_555_ = stack[2].m_obj;
lean_object* v_a_556_ = stack[3].m_obj;
lean_object* v_a_557_ = stack[4].m_obj;
lean_object* v_a_558_ = stack[5].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_553_, v_k_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg___boxed(lean_object* v_es_576_, lean_object* v_k_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_576_, v_k_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
lean_object* l_Lean_Meta_generalizeTelescope(lean_object* v_00_u03b1_584_, lean_object* v_es_585_, lean_object* v_k_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_585_, v_k_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
return v___x_592_;
}
}
LEAN_EXPORT void l_Lean_Meta_generalizeTelescope_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_585_ = stack[1].m_obj;
lean_object* v_k_586_ = stack[2].m_obj;
lean_object* v_a_587_ = stack[3].m_obj;
lean_object* v_a_588_ = stack[4].m_obj;
lean_object* v_a_589_ = stack[5].m_obj;
lean_object* v_a_590_ = stack[6].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_Meta_generalizeTelescope(lean_box(0), v_es_585_, v_k_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___boxed(lean_object* v_00_u03b1_594_, lean_object* v_es_595_, lean_object* v_k_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Meta_generalizeTelescope(v_00_u03b1_594_, v_es_595_, v_k_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_602_;
}
}
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_GeneralizeTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_GeneralizeTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_GeneralizeTelescope(builtin);
}
#ifdef __cplusplus
}
#endif
