// Lean compiler output
// Module: Lean.Meta.Sym.IsClass
// Imports: public import Lean.Meta.Sym.SymM
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
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 8:
{
lean_object* v_body_2_; 
v_body_2_ = lean_ctor_get(v_x_1_, 3);
v_x_1_ = v_body_2_;
goto _start;
}
case 7:
{
lean_object* v_body_4_; 
v_body_4_ = lean_ctor_get(v_x_1_, 2);
v_x_1_ = v_body_4_;
goto _start;
}
case 10:
{
lean_object* v_expr_6_; 
v_expr_6_ = lean_ctor_get(v_x_1_, 1);
v_x_1_ = v_expr_6_;
goto _start;
}
case 5:
{
lean_object* v_fn_8_; 
v_fn_8_ = lean_ctor_get(v_x_1_, 0);
v_x_1_ = v_fn_8_;
goto _start;
}
default: 
{
lean_inc_ref(v_x_1_);
return v_x_1_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead(v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f(lean_object* v_env_12_, lean_object* v_head_13_){
_start:
{
if (lean_obj_tag(v_head_13_) == 4)
{
lean_object* v_declName_14_; uint8_t v___x_15_; 
v_declName_14_ = lean_ctor_get(v_head_13_, 0);
v___x_15_ = l_Lean_isClass(v_env_12_, v_declName_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
else
{
lean_object* v___x_17_; 
lean_inc(v_declName_14_);
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_declName_14_);
return v___x_17_;
}
}
else
{
lean_object* v___x_18_; 
lean_dec_ref(v_env_12_);
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f___boxed(lean_object* v_env_19_, lean_object* v_head_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f(v_env_19_, v_head_20_);
lean_dec_ref(v_head_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg(lean_object* v_e_22_, lean_object* v___y_23_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = l_Lean_Expr_hasMVar(v_e_22_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_22_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; lean_object* v_mctx_28_; lean_object* v___x_29_; lean_object* v_fst_30_; lean_object* v_snd_31_; lean_object* v___x_32_; lean_object* v_cache_33_; lean_object* v_zetaDeltaFVarIds_34_; lean_object* v_postponed_35_; lean_object* v_diag_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_45_; 
v___x_27_ = lean_st_ref_get(v___y_23_);
v_mctx_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_ref(v_mctx_28_);
lean_dec(v___x_27_);
v___x_29_ = l_Lean_instantiateMVarsCore(v_mctx_28_, v_e_22_);
v_fst_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_fst_30_);
v_snd_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_snd_31_);
lean_dec_ref(v___x_29_);
v___x_32_ = lean_st_ref_take(v___y_23_);
v_cache_33_ = lean_ctor_get(v___x_32_, 1);
v_zetaDeltaFVarIds_34_ = lean_ctor_get(v___x_32_, 2);
v_postponed_35_ = lean_ctor_get(v___x_32_, 3);
v_diag_36_ = lean_ctor_get(v___x_32_, 4);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v___x_32_, 0);
lean_dec(v_unused_46_);
v___x_38_ = v___x_32_;
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_diag_36_);
lean_inc(v_postponed_35_);
lean_inc(v_zetaDeltaFVarIds_34_);
lean_inc(v_cache_33_);
lean_dec(v___x_32_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_45_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v_snd_31_);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_snd_31_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_cache_33_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_zetaDeltaFVarIds_34_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_postponed_35_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_diag_36_);
v___x_41_ = v_reuseFailAlloc_44_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_st_ref_put(v___y_23_, v___x_41_);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v_fst_30_);
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg___boxed(lean_object* v_e_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg(v_e_47_, v___y_48_);
lean_dec(v___y_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0(lean_object* v_e_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg(v_e_51_, v___y_53_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___boxed(lean_object* v_e_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0(v_e_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_keys_65_, lean_object* v_i_66_, lean_object* v_k_67_){
_start:
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = lean_array_get_size(v_keys_65_);
v___x_69_ = lean_nat_dec_lt(v_i_66_, v___x_68_);
if (v___x_69_ == 0)
{
lean_dec(v_i_66_);
return v___x_69_;
}
else
{
lean_object* v_k_x27_70_; uint8_t v___x_71_; 
v_k_x27_70_ = lean_array_fget_borrowed(v_keys_65_, v_i_66_);
v___x_71_ = l_Lean_instBEqMVarId_beq(v_k_67_, v_k_x27_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_i_66_, v___x_72_);
lean_dec(v_i_66_);
v_i_66_ = v___x_73_;
goto _start;
}
else
{
lean_dec(v_i_66_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_keys_75_, lean_object* v_i_76_, lean_object* v_k_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_keys_75_, v_i_76_, v_k_77_);
lean_dec(v_k_77_);
lean_dec_ref(v_keys_75_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_80_, size_t v_x_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_es_83_; lean_object* v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v_j_87_; lean_object* v___x_88_; 
v_es_83_ = lean_ctor_get(v_x_80_, 0);
v___x_84_ = lean_box(2);
v___x_85_ = ((size_t)31ULL);
v___x_86_ = lean_usize_land(v_x_81_, v___x_85_);
v_j_87_ = lean_usize_to_nat(v___x_86_);
v___x_88_ = lean_array_get_borrowed(v___x_84_, v_es_83_, v_j_87_);
lean_dec(v_j_87_);
switch(lean_obj_tag(v___x_88_))
{
case 0:
{
lean_object* v_key_89_; uint8_t v___x_90_; 
v_key_89_ = lean_ctor_get(v___x_88_, 0);
v___x_90_ = l_Lean_instBEqMVarId_beq(v_x_82_, v_key_89_);
return v___x_90_;
}
case 1:
{
lean_object* v_node_91_; size_t v___x_92_; size_t v___x_93_; 
v_node_91_ = lean_ctor_get(v___x_88_, 0);
v___x_92_ = ((size_t)5ULL);
v___x_93_ = lean_usize_shift_right(v_x_81_, v___x_92_);
v_x_80_ = v_node_91_;
v_x_81_ = v___x_93_;
goto _start;
}
default: 
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
}
else
{
lean_object* v_ks_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_ks_96_ = lean_ctor_get(v_x_80_, 0);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_ks_96_, v___x_97_, v_x_82_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
size_t v_x_2116__boxed_102_; uint8_t v_res_103_; lean_object* v_r_104_; 
v_x_2116__boxed_102_ = lean_unbox_usize(v_x_100_);
lean_dec(v_x_100_);
v_res_103_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg(v_x_99_, v_x_2116__boxed_102_, v_x_101_);
lean_dec(v_x_101_);
lean_dec_ref(v_x_99_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint64_t v___x_107_; size_t v___x_108_; uint8_t v___x_109_; 
v___x_107_ = l_Lean_instHashableMVarId_hash(v_x_106_);
v___x_108_ = lean_uint64_to_usize(v___x_107_);
v___x_109_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg(v_x_105_, v___x_108_, v_x_106_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg(v_x_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec_ref(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg(lean_object* v_mvarId_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; lean_object* v_mctx_118_; lean_object* v_eAssignment_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_117_ = lean_st_ref_get(v___y_115_);
v_mctx_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_mctx_118_);
lean_dec(v___x_117_);
v_eAssignment_119_ = lean_ctor_get(v_mctx_118_, 8);
lean_inc_ref(v_eAssignment_119_);
lean_dec_ref(v_mctx_118_);
v___x_120_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg(v_eAssignment_119_, v_mvarId_114_);
lean_dec_ref(v_eAssignment_119_);
v___x_121_ = lean_box(v___x_120_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg(v_mvarId_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec(v_mvarId_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg(lean_object* v_mvarId_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; lean_object* v_mctx_131_; lean_object* v_dAssignment_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_130_ = lean_st_ref_get(v___y_128_);
v_mctx_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc_ref(v_mctx_131_);
lean_dec(v___x_130_);
v_dAssignment_132_ = lean_ctor_get(v_mctx_131_, 9);
lean_inc_ref(v_dAssignment_132_);
lean_dec_ref(v_mctx_131_);
v___x_133_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg(v_dAssignment_132_, v_mvarId_127_);
lean_dec_ref(v_dAssignment_132_);
v___x_134_ = lean_box(v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg___boxed(lean_object* v_mvarId_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg(v_mvarId_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec(v_mvarId_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f(lean_object* v_type_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead(v_type_140_);
if (lean_obj_tag(v___x_160_) == 2)
{
lean_object* v_mvarId_161_; lean_object* v___x_162_; lean_object* v_a_163_; uint8_t v___x_164_; 
v_mvarId_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_mvarId_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg(v_mvarId_161_, v_a_142_);
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref(v___x_162_);
v___x_164_ = lean_unbox(v_a_163_);
lean_dec(v_a_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_175_; 
v___x_165_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg(v_mvarId_161_, v_a_142_);
lean_dec(v_mvarId_161_);
v_a_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_175_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_175_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_175_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
uint8_t v___x_170_; 
v___x_170_ = lean_unbox(v_a_166_);
lean_dec(v_a_166_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_dec_ref(v_type_140_);
v___x_171_ = lean_box(0);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_171_);
v___x_173_ = v___x_168_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
else
{
lean_del_object(v___x_168_);
goto v___jp_146_;
}
}
}
else
{
lean_dec(v_mvarId_161_);
goto v___jp_146_;
}
}
else
{
lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec_ref(v_type_140_);
v___x_176_ = lean_st_ref_get(v_a_144_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_176_);
v___x_178_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f(v_env_177_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
v___jp_146_:
{
lean_object* v___x_147_; lean_object* v_env_148_; lean_object* v___x_149_; lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_159_; 
v___x_147_ = lean_st_ref_get(v_a_144_);
v_env_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc_ref(v_env_148_);
lean_dec(v___x_147_);
v___x_149_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_isClass_x3f_spec__0___redArg(v_type_140_, v_a_142_);
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_159_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_getConclusionHead(v_a_150_);
lean_dec(v_a_150_);
v___x_155_ = l___private_Lean_Meta_Sym_IsClass_0__Lean_Meta_Sym_isClassHead_x3f(v_env_148_, v___x_154_);
lean_dec_ref(v___x_154_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_155_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isClass_x3f___boxed(lean_object* v_type_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_Sym_isClass_x3f(v_type_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1(lean_object* v_mvarId_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___redArg(v_mvarId_187_, v___y_189_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1___boxed(lean_object* v_mvarId_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1(v_mvarId_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v_mvarId_194_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2(lean_object* v_mvarId_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___redArg(v_mvarId_201_, v___y_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2___boxed(lean_object* v_mvarId_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_MVarId_isDelayedAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__2(v_mvarId_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v_mvarId_208_);
return v_res_214_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1(lean_object* v_00_u03b2_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___redArg(v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1(v_00_u03b2_219_, v_x_220_, v_x_221_);
lean_dec(v_x_221_);
lean_dec_ref(v_x_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_224_, lean_object* v_x_225_, size_t v_x_226_, lean_object* v_x_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___redArg(v_x_225_, v_x_226_, v_x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
size_t v_x_2309__boxed_233_; uint8_t v_res_234_; lean_object* v_r_235_; 
v_x_2309__boxed_233_ = lean_unbox_usize(v_x_231_);
lean_dec(v_x_231_);
v_res_234_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2(v_00_u03b2_229_, v_x_230_, v_x_2309__boxed_233_, v_x_232_);
lean_dec(v_x_232_);
lean_dec_ref(v_x_230_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_236_, lean_object* v_keys_237_, lean_object* v_vals_238_, lean_object* v_heq_239_, lean_object* v_i_240_, lean_object* v_k_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_keys_237_, v_i_240_, v_k_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_243_, lean_object* v_keys_244_, lean_object* v_vals_245_, lean_object* v_heq_246_, lean_object* v_i_247_, lean_object* v_k_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_isClass_x3f_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_243_, v_keys_244_, v_vals_245_, v_heq_246_, v_i_247_, v_k_248_);
lean_dec(v_k_248_);
lean_dec_ref(v_vals_245_);
lean_dec_ref(v_keys_244_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_IsClass(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_IsClass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_IsClass(builtin);
}
#ifdef __cplusplus
}
#endif
