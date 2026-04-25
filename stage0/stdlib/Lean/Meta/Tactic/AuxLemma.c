// Lean compiler output
// Module: Lean.Meta.Tactic.AuxLemma
// Imports: public import Lean.AddDecl public import Lean.DefEqAttrib
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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqAuxLemmaKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instBEqAuxLemmaKey___closed__0 = (const lean_object*)&l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instBEqAuxLemmaKey = (const lean_object*)&l_Lean_Meta_instBEqAuxLemmaKey___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableAuxLemmaKey_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_instHashableAuxLemmaKey___closed__0 = (const lean_object*)&l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instHashableAuxLemmaKey = (const lean_object*)&l_Lean_Meta_instHashableAuxLemmaKey___closed__0_value;
static lean_once_cell_t l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAuxLemmas_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAuxLemmas;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_auxLemmasExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkAuxLemma___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkAuxLemma___closed__0;
static lean_once_cell_t l_Lean_Meta_mkAuxLemma___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkAuxLemma___closed__1;
static lean_once_cell_t l_Lean_Meta_mkAuxLemma___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkAuxLemma___closed__2;
static lean_once_cell_t l_Lean_Meta_mkAuxLemma___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkAuxLemma___closed__3;
static const lean_string_object l_Lean_Meta_mkAuxLemma___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_proof"};
static const lean_object* l_Lean_Meta_mkAuxLemma___closed__4 = (const lean_object*)&l_Lean_Meta_mkAuxLemma___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkAuxLemma___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkAuxLemma___closed__4_value),LEAN_SCALAR_PTR_LITERAL(118, 32, 192, 173, 72, 22, 234, 250)}};
static const lean_object* l_Lean_Meta_mkAuxLemma___closed__5 = (const lean_object*)&l_Lean_Meta_mkAuxLemma___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqAuxLemmaKey_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_type_3_; uint8_t v_isPrivate_4_; lean_object* v_type_5_; uint8_t v_isPrivate_6_; uint8_t v___x_7_; 
v_type_3_ = lean_ctor_get(v_x_1_, 0);
v_isPrivate_4_ = lean_ctor_get_uint8(v_x_1_, sizeof(void*)*1);
v_type_5_ = lean_ctor_get(v_x_2_, 0);
v_isPrivate_6_ = lean_ctor_get_uint8(v_x_2_, sizeof(void*)*1);
v___x_7_ = lean_expr_eqv(v_type_3_, v_type_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
if (v_isPrivate_4_ == 0)
{
if (v_isPrivate_6_ == 0)
{
return v___x_7_;
}
else
{
return v_isPrivate_4_;
}
}
else
{
return v_isPrivate_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAuxLemmaKey_beq___boxed(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_8_, v_x_9_);
lean_dec_ref(v_x_9_);
lean_dec_ref(v_x_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableAuxLemmaKey_hash(lean_object* v_x_14_){
_start:
{
lean_object* v_type_15_; uint8_t v_isPrivate_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; 
v_type_15_ = lean_ctor_get(v_x_14_, 0);
v_isPrivate_16_ = lean_ctor_get_uint8(v_x_14_, sizeof(void*)*1);
v___x_17_ = 0ULL;
v___x_18_ = l_Lean_Expr_hash(v_type_15_);
v___x_19_ = lean_uint64_mix_hash(v___x_17_, v___x_18_);
if (v_isPrivate_16_ == 0)
{
uint64_t v___x_20_; uint64_t v___x_21_; 
v___x_20_ = 13ULL;
v___x_21_ = lean_uint64_mix_hash(v___x_19_, v___x_20_);
return v___x_21_;
}
else
{
uint64_t v___x_22_; uint64_t v___x_23_; 
v___x_22_ = 11ULL;
v___x_23_ = lean_uint64_mix_hash(v___x_19_, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableAuxLemmaKey_hash___boxed(lean_object* v_x_24_){
_start:
{
uint64_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_24_);
lean_dec_ref(v_x_24_);
v_r_26_ = lean_box_uint64(v_res_25_);
return v_r_26_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_29_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__0);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas_default(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(lean_object* v___x_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v___x_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(v___x_37_);
return v_res_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_40_; lean_object* v___f_41_; 
v___x_40_ = lean_obj_once(&l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1, &l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1_once, _init_l_Lean_Meta_instInhabitedAuxLemmas_default___closed__1);
v___f_41_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_41_, 0, v___x_40_);
return v___f_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___f_43_ = lean_obj_once(&l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_box(1);
v___x_46_ = l_Lean_registerEnvExtension___redArg(v___f_43_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2____boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object* v_kind_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; lean_object* v_auxDeclNGen_53_; lean_object* v___x_54_; lean_object* v_env_55_; lean_object* v___x_56_; lean_object* v_fst_57_; lean_object* v_snd_58_; lean_object* v___x_59_; lean_object* v_env_60_; lean_object* v_nextMacroScope_61_; lean_object* v_ngen_62_; lean_object* v_traceState_63_; lean_object* v_cache_64_; lean_object* v_messages_65_; lean_object* v_infoState_66_; lean_object* v_snapshotTasks_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_76_; 
v___x_52_ = lean_st_ref_get(v___y_50_);
v_auxDeclNGen_53_ = lean_ctor_get(v___x_52_, 3);
lean_inc_ref(v_auxDeclNGen_53_);
lean_dec(v___x_52_);
v___x_54_ = lean_st_ref_get(v___y_50_);
v_env_55_ = lean_ctor_get(v___x_54_, 0);
lean_inc_ref(v_env_55_);
lean_dec(v___x_54_);
v___x_56_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_55_, v_auxDeclNGen_53_, v_kind_49_);
v_fst_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_fst_57_);
v_snd_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_snd_58_);
lean_dec_ref(v___x_56_);
v___x_59_ = lean_st_ref_take(v___y_50_);
v_env_60_ = lean_ctor_get(v___x_59_, 0);
v_nextMacroScope_61_ = lean_ctor_get(v___x_59_, 1);
v_ngen_62_ = lean_ctor_get(v___x_59_, 2);
v_traceState_63_ = lean_ctor_get(v___x_59_, 4);
v_cache_64_ = lean_ctor_get(v___x_59_, 5);
v_messages_65_ = lean_ctor_get(v___x_59_, 6);
v_infoState_66_ = lean_ctor_get(v___x_59_, 7);
v_snapshotTasks_67_ = lean_ctor_get(v___x_59_, 8);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_76_ == 0)
{
lean_object* v_unused_77_; 
v_unused_77_ = lean_ctor_get(v___x_59_, 3);
lean_dec(v_unused_77_);
v___x_69_ = v___x_59_;
v_isShared_70_ = v_isSharedCheck_76_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_snapshotTasks_67_);
lean_inc(v_infoState_66_);
lean_inc(v_messages_65_);
lean_inc(v_cache_64_);
lean_inc(v_traceState_63_);
lean_inc(v_ngen_62_);
lean_inc(v_nextMacroScope_61_);
lean_inc(v_env_60_);
lean_dec(v___x_59_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_76_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 3, v_snd_58_);
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_env_60_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_nextMacroScope_61_);
lean_ctor_set(v_reuseFailAlloc_75_, 2, v_ngen_62_);
lean_ctor_set(v_reuseFailAlloc_75_, 3, v_snd_58_);
lean_ctor_set(v_reuseFailAlloc_75_, 4, v_traceState_63_);
lean_ctor_set(v_reuseFailAlloc_75_, 5, v_cache_64_);
lean_ctor_set(v_reuseFailAlloc_75_, 6, v_messages_65_);
lean_ctor_set(v_reuseFailAlloc_75_, 7, v_infoState_66_);
lean_ctor_set(v_reuseFailAlloc_75_, 8, v_snapshotTasks_67_);
v___x_72_ = v_reuseFailAlloc_75_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_st_ref_set(v___y_50_, v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v_fst_57_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg___boxed(lean_object* v_kind_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_78_, v___y_79_);
lean_dec(v___y_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(lean_object* v_kind_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v_kind_82_, v___y_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___boxed(lean_object* v_kind_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0(v_kind_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_ks_100_; lean_object* v_vs_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_125_; 
v_ks_100_ = lean_ctor_get(v_x_96_, 0);
v_vs_101_ = lean_ctor_get(v_x_96_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_125_ == 0)
{
v___x_103_ = v_x_96_;
v_isShared_104_ = v_isSharedCheck_125_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_vs_101_);
lean_inc(v_ks_100_);
lean_dec(v_x_96_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_125_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_array_get_size(v_ks_100_);
v___x_106_ = lean_nat_dec_lt(v_x_97_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_dec(v_x_97_);
v___x_107_ = lean_array_push(v_ks_100_, v_x_98_);
v___x_108_ = lean_array_push(v_vs_101_, v_x_99_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_108_);
lean_ctor_set(v___x_103_, 0, v___x_107_);
v___x_110_ = v___x_103_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
lean_object* v_k_x27_112_; uint8_t v___x_113_; 
v_k_x27_112_ = lean_array_fget_borrowed(v_ks_100_, v_x_97_);
v___x_113_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_98_, v_k_x27_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; 
if (v_isShared_104_ == 0)
{
v___x_115_ = v___x_103_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_ks_100_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_vs_101_);
v___x_115_ = v_reuseFailAlloc_119_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_x_97_, v___x_116_);
lean_dec(v_x_97_);
v_x_96_ = v___x_115_;
v_x_97_ = v___x_117_;
goto _start;
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = lean_array_fset(v_ks_100_, v_x_97_, v_x_98_);
v___x_121_ = lean_array_fset(v_vs_101_, v_x_97_, v_x_99_);
lean_dec(v_x_97_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_121_);
lean_ctor_set(v___x_103_, 0, v___x_120_);
v___x_123_ = v___x_103_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(lean_object* v_n_126_, lean_object* v_k_127_, lean_object* v_v_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5___redArg(v_n_126_, v___x_129_, v_k_127_, v_v_128_);
return v___x_130_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; 
v___x_131_ = ((size_t)5ULL);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_shift_left(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; 
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__0);
v___x_136_ = lean_usize_sub(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(lean_object* v_x_138_, size_t v_x_139_, size_t v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_es_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; lean_object* v_j_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_es_143_ = lean_ctor_get(v_x_138_, 0);
v___x_144_ = ((size_t)5ULL);
v___x_145_ = ((size_t)1ULL);
v___x_146_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_147_ = lean_usize_land(v_x_139_, v___x_146_);
v_j_148_ = lean_usize_to_nat(v___x_147_);
v___x_149_ = lean_array_get_size(v_es_143_);
v___x_150_ = lean_nat_dec_lt(v_j_148_, v___x_149_);
if (v___x_150_ == 0)
{
lean_dec(v_j_148_);
lean_dec(v_x_142_);
lean_dec_ref(v_x_141_);
return v_x_138_;
}
else
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_187_; 
lean_inc_ref(v_es_143_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_x_138_, 0);
lean_dec(v_unused_188_);
v___x_152_ = v_x_138_;
v_isShared_153_ = v_isSharedCheck_187_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_x_138_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_187_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_v_154_; lean_object* v___x_155_; lean_object* v_xs_x27_156_; lean_object* v___y_158_; 
v_v_154_ = lean_array_fget(v_es_143_, v_j_148_);
v___x_155_ = lean_box(0);
v_xs_x27_156_ = lean_array_fset(v_es_143_, v_j_148_, v___x_155_);
switch(lean_obj_tag(v_v_154_))
{
case 0:
{
lean_object* v_key_163_; lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
v_key_163_ = lean_ctor_get(v_v_154_, 0);
v_val_164_ = lean_ctor_get(v_v_154_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_v_154_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v_v_154_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_inc(v_key_163_);
lean_dec(v_v_154_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_141_, v_key_163_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_del_object(v___x_166_);
v___x_169_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_163_, v_val_164_, v_x_141_, v_x_142_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
v___y_158_ = v___x_170_;
goto v___jp_157_;
}
else
{
lean_object* v___x_172_; 
lean_dec(v_val_164_);
lean_dec(v_key_163_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_x_142_);
lean_ctor_set(v___x_166_, 0, v_x_141_);
v___x_172_ = v___x_166_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_x_141_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_x_142_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
v___y_158_ = v___x_172_;
goto v___jp_157_;
}
}
}
}
case 1:
{
lean_object* v_node_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v_node_175_ = lean_ctor_get(v_v_154_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_v_154_);
if (v_isSharedCheck_185_ == 0)
{
v___x_177_ = v_v_154_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_node_175_);
lean_dec(v_v_154_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
size_t v___x_179_; size_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_179_ = lean_usize_shift_right(v_x_139_, v___x_144_);
v___x_180_ = lean_usize_add(v_x_140_, v___x_145_);
v___x_181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_node_175_, v___x_179_, v___x_180_, v_x_141_, v_x_142_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_181_);
v___x_183_ = v___x_177_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v___y_158_ = v___x_183_;
goto v___jp_157_;
}
}
}
default: 
{
lean_object* v___x_186_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_x_141_);
lean_ctor_set(v___x_186_, 1, v_x_142_);
v___y_158_ = v___x_186_;
goto v___jp_157_;
}
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_array_fset(v_xs_x27_156_, v_j_148_, v___y_158_);
lean_dec(v_j_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_159_);
v___x_161_ = v___x_152_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
else
{
lean_object* v_ks_189_; lean_object* v_vs_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_210_; 
v_ks_189_ = lean_ctor_get(v_x_138_, 0);
v_vs_190_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_210_ == 0)
{
v___x_192_ = v_x_138_;
v_isShared_193_ = v_isSharedCheck_210_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_vs_190_);
lean_inc(v_ks_189_);
lean_dec(v_x_138_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_210_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_ks_189_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_vs_190_);
v___x_195_ = v_reuseFailAlloc_209_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v_newNode_196_; uint8_t v___y_198_; size_t v___x_204_; uint8_t v___x_205_; 
v_newNode_196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v___x_195_, v_x_141_, v_x_142_);
v___x_204_ = ((size_t)7ULL);
v___x_205_ = lean_usize_dec_le(v___x_204_, v_x_140_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_196_);
v___x_207_ = lean_unsigned_to_nat(4u);
v___x_208_ = lean_nat_dec_lt(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
v___y_198_ = v___x_208_;
goto v___jp_197_;
}
else
{
v___y_198_ = v___x_205_;
goto v___jp_197_;
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
lean_object* v_ks_199_; lean_object* v_vs_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_ks_199_ = lean_ctor_get(v_newNode_196_, 0);
lean_inc_ref(v_ks_199_);
v_vs_200_ = lean_ctor_get(v_newNode_196_, 1);
lean_inc_ref(v_vs_200_);
lean_dec_ref(v_newNode_196_);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__2);
v___x_203_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_x_140_, v_ks_199_, v_vs_200_, v___x_201_, v___x_202_);
lean_dec_ref(v_vs_200_);
lean_dec_ref(v_ks_199_);
return v___x_203_;
}
else
{
return v_newNode_196_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(size_t v_depth_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_i_214_, lean_object* v_entries_215_){
_start:
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_array_get_size(v_keys_212_);
v___x_217_ = lean_nat_dec_lt(v_i_214_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_i_214_);
return v_entries_215_;
}
else
{
lean_object* v_k_218_; lean_object* v_v_219_; uint64_t v___x_220_; size_t v_h_221_; size_t v___x_222_; lean_object* v___x_223_; size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v_h_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_k_218_ = lean_array_fget_borrowed(v_keys_212_, v_i_214_);
v_v_219_ = lean_array_fget_borrowed(v_vals_213_, v_i_214_);
v___x_220_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_k_218_);
v_h_221_ = lean_uint64_to_usize(v___x_220_);
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_sub(v_depth_211_, v___x_224_);
v___x_226_ = lean_usize_mul(v___x_222_, v___x_225_);
v_h_227_ = lean_usize_shift_right(v_h_221_, v___x_226_);
v___x_228_ = lean_nat_add(v_i_214_, v___x_223_);
lean_dec(v_i_214_);
lean_inc(v_v_219_);
lean_inc(v_k_218_);
v___x_229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_entries_215_, v_h_227_, v_depth_211_, v_k_218_, v_v_219_);
v_i_214_ = v___x_228_;
v_entries_215_ = v___x_229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_231_, lean_object* v_keys_232_, lean_object* v_vals_233_, lean_object* v_i_234_, lean_object* v_entries_235_){
_start:
{
size_t v_depth_boxed_236_; lean_object* v_res_237_; 
v_depth_boxed_236_ = lean_unbox_usize(v_depth_231_);
lean_dec(v_depth_231_);
v_res_237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_boxed_236_, v_keys_232_, v_vals_233_, v_i_234_, v_entries_235_);
lean_dec_ref(v_vals_233_);
lean_dec_ref(v_keys_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___boxed(lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
size_t v_x_3883__boxed_243_; size_t v_x_3884__boxed_244_; lean_object* v_res_245_; 
v_x_3883__boxed_243_ = lean_unbox_usize(v_x_239_);
lean_dec(v_x_239_);
v_x_3884__boxed_244_ = lean_unbox_usize(v_x_240_);
lean_dec(v_x_240_);
v_res_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_238_, v_x_3883__boxed_243_, v_x_3884__boxed_244_, v_x_241_, v_x_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
uint64_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; 
v___x_249_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_247_);
v___x_250_ = lean_uint64_to_usize(v___x_249_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_246_, v___x_250_, v___x_251_, v_x_247_, v_x_248_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___lam__0(lean_object* v_a_253_, lean_object* v_levelParams_254_, lean_object* v___x_255_, lean_object* v_x_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_a_253_);
lean_ctor_set(v___x_257_, 1, v_levelParams_254_);
v___x_258_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_256_, v___x_255_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_259_, lean_object* v_vals_260_, lean_object* v_i_261_, lean_object* v_k_262_){
_start:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_array_get_size(v_keys_259_);
v___x_264_ = lean_nat_dec_lt(v_i_261_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_i_261_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_k_x27_266_; uint8_t v___x_267_; 
v_k_x27_266_ = lean_array_fget_borrowed(v_keys_259_, v_i_261_);
v___x_267_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_k_262_, v_k_x27_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_i_261_, v___x_268_);
lean_dec(v_i_261_);
v_i_261_ = v___x_269_;
goto _start;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_array_fget_borrowed(v_vals_260_, v_i_261_);
lean_dec(v_i_261_);
lean_inc(v___x_271_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_273_, lean_object* v_vals_274_, lean_object* v_i_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_keys_273_, v_vals_274_, v_i_275_, v_k_276_);
lean_dec_ref(v_k_276_);
lean_dec_ref(v_vals_274_);
lean_dec_ref(v_keys_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(lean_object* v_x_278_, size_t v_x_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v_es_281_; lean_object* v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v_j_286_; lean_object* v___x_287_; 
v_es_281_ = lean_ctor_get(v_x_278_, 0);
v___x_282_ = lean_box(2);
v___x_283_ = ((size_t)5ULL);
v___x_284_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_285_ = lean_usize_land(v_x_279_, v___x_284_);
v_j_286_ = lean_usize_to_nat(v___x_285_);
v___x_287_ = lean_array_get_borrowed(v___x_282_, v_es_281_, v_j_286_);
lean_dec(v_j_286_);
switch(lean_obj_tag(v___x_287_))
{
case 0:
{
lean_object* v_key_288_; lean_object* v_val_289_; uint8_t v___x_290_; 
v_key_288_ = lean_ctor_get(v___x_287_, 0);
v_val_289_ = lean_ctor_get(v___x_287_, 1);
v___x_290_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_280_, v_key_288_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_box(0);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
lean_inc(v_val_289_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_val_289_);
return v___x_292_;
}
}
case 1:
{
lean_object* v_node_293_; size_t v___x_294_; 
v_node_293_ = lean_ctor_get(v___x_287_, 0);
v___x_294_ = lean_usize_shift_right(v_x_279_, v___x_283_);
v_x_278_ = v_node_293_;
v_x_279_ = v___x_294_;
goto _start;
}
default: 
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
}
}
else
{
lean_object* v_ks_297_; lean_object* v_vs_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_ks_297_ = lean_ctor_get(v_x_278_, 0);
v_vs_298_ = lean_ctor_get(v_x_278_, 1);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_ks_297_, v_vs_298_, v___x_299_, v_x_280_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
size_t v_x_4093__boxed_304_; lean_object* v_res_305_; 
v_x_4093__boxed_304_ = lean_unbox_usize(v_x_302_);
lean_dec(v_x_302_);
v_res_305_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_x_301_, v_x_4093__boxed_304_, v_x_303_);
lean_dec_ref(v_x_303_);
lean_dec_ref(v_x_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
uint64_t v___x_308_; size_t v___x_309_; lean_object* v___x_310_; 
v___x_308_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_x_306_, v___x_309_, v_x_307_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v_x_311_, v_x_312_);
lean_dec_ref(v_x_312_);
lean_dec_ref(v_x_311_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 1;
return v___x_316_;
}
else
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
}
else
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
else
{
lean_object* v_head_319_; lean_object* v_tail_320_; lean_object* v_head_321_; lean_object* v_tail_322_; uint8_t v___x_323_; 
v_head_319_ = lean_ctor_get(v_x_314_, 0);
v_tail_320_ = lean_ctor_get(v_x_314_, 1);
v_head_321_ = lean_ctor_get(v_x_315_, 0);
v_tail_322_ = lean_ctor_get(v_x_315_, 1);
v___x_323_ = lean_name_eq(v_head_319_, v_head_321_);
if (v___x_323_ == 0)
{
return v___x_323_;
}
else
{
v_x_314_ = v_tail_320_;
v_x_315_ = v_tail_322_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(v_x_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec(v_x_325_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__0(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__1(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__0, &l_Lean_Meta_mkAuxLemma___closed__0_once, _init_l_Lean_Meta_mkAuxLemma___closed__0);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__2(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__1, &l_Lean_Meta_mkAuxLemma___closed__1_once, _init_l_Lean_Meta_mkAuxLemma___closed__1);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__3(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__1, &l_Lean_Meta_mkAuxLemma___closed__1_once, _init_l_Lean_Meta_mkAuxLemma___closed__1);
v___x_335_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
lean_ctor_set(v___x_335_, 4, v___x_334_);
lean_ctor_set(v___x_335_, 5, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_339_, lean_object* v_type_340_, lean_object* v_value_341_, lean_object* v_kind_x3f_342_, uint8_t v_cache_343_, uint8_t v_inferRfl_344_, uint8_t v_forceExpose_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; lean_object* v_env_352_; lean_object* v___x_353_; lean_object* v_asyncMode_354_; uint8_t v_isExporting_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; uint8_t v___y_432_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___x_536_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v___y_562_; uint8_t v___y_581_; 
v___x_351_ = lean_st_ref_get(v_a_349_);
v_env_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc_ref_n(v_env_352_, 2);
lean_dec(v___x_351_);
v___x_353_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_354_ = lean_ctor_get(v___x_353_, 2);
v_isExporting_355_ = lean_ctor_get_uint8(v_env_352_, sizeof(void*)*8);
v___x_356_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_357_ = lean_box(0);
v___x_536_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_356_, v___x_353_, v_env_352_, v_asyncMode_354_, v___x_357_);
if (v_isExporting_355_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = 1;
v___y_581_ = v___x_585_;
goto v___jp_580_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = 0;
v___y_581_ = v___x_586_;
goto v___jp_580_;
}
v___jp_358_:
{
lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v_nextMacroScope_365_; lean_object* v_ngen_366_; lean_object* v_auxDeclNGen_367_; lean_object* v_traceState_368_; lean_object* v_messages_369_; lean_object* v_infoState_370_; lean_object* v_snapshotTasks_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_397_; 
v___x_363_ = lean_st_ref_take(v___y_362_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
v_nextMacroScope_365_ = lean_ctor_get(v___x_363_, 1);
v_ngen_366_ = lean_ctor_get(v___x_363_, 2);
v_auxDeclNGen_367_ = lean_ctor_get(v___x_363_, 3);
v_traceState_368_ = lean_ctor_get(v___x_363_, 4);
v_messages_369_ = lean_ctor_get(v___x_363_, 6);
v_infoState_370_ = lean_ctor_get(v___x_363_, 7);
v_snapshotTasks_371_ = lean_ctor_get(v___x_363_, 8);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_363_, 5);
lean_dec(v_unused_398_);
v___x_373_ = v___x_363_;
v_isShared_374_ = v_isSharedCheck_397_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snapshotTasks_371_);
lean_inc(v_infoState_370_);
lean_inc(v_messages_369_);
lean_inc(v_traceState_368_);
lean_inc(v_auxDeclNGen_367_);
lean_inc(v_ngen_366_);
lean_inc(v_nextMacroScope_365_);
lean_inc(v_env_364_);
lean_dec(v___x_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_397_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = l_Lean_EnvExtension_modifyState___redArg(v___x_353_, v_env_364_, v___y_359_, v_asyncMode_354_, v___x_357_);
v___x_376_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__2, &l_Lean_Meta_mkAuxLemma___closed__2_once, _init_l_Lean_Meta_mkAuxLemma___closed__2);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 5, v___x_376_);
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_nextMacroScope_365_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_ngen_366_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_auxDeclNGen_367_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_traceState_368_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_messages_369_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_infoState_370_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_snapshotTasks_371_);
v___x_378_ = v_reuseFailAlloc_396_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_mctx_381_; lean_object* v_zetaDeltaFVarIds_382_; lean_object* v_postponed_383_; lean_object* v_diag_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_394_; 
v___x_379_ = lean_st_ref_set(v___y_362_, v___x_378_);
v___x_380_ = lean_st_ref_take(v___y_361_);
v_mctx_381_ = lean_ctor_get(v___x_380_, 0);
v_zetaDeltaFVarIds_382_ = lean_ctor_get(v___x_380_, 2);
v_postponed_383_ = lean_ctor_get(v___x_380_, 3);
v_diag_384_ = lean_ctor_get(v___x_380_, 4);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v___x_380_, 1);
lean_dec(v_unused_395_);
v___x_386_ = v___x_380_;
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_diag_384_);
lean_inc(v_postponed_383_);
lean_inc(v_zetaDeltaFVarIds_382_);
lean_inc(v_mctx_381_);
lean_dec(v___x_380_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_394_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__3, &l_Lean_Meta_mkAuxLemma___closed__3_once, _init_l_Lean_Meta_mkAuxLemma___closed__3);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v___x_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_mctx_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_zetaDeltaFVarIds_382_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_postponed_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_diag_384_);
v___x_390_ = v_reuseFailAlloc_393_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_st_ref_set(v___y_361_, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___y_360_);
return v___x_392_;
}
}
}
}
}
v___jp_399_:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_addDecl(v___y_406_, v_forceExpose_345_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_dec_ref(v___x_407_);
if (v_inferRfl_344_ == 0)
{
v___y_359_ = v___y_400_;
v___y_360_ = v___y_405_;
v___y_361_ = v___y_402_;
v___y_362_ = v___y_404_;
goto v___jp_358_;
}
else
{
lean_object* v___x_408_; 
lean_inc(v___y_405_);
v___x_408_ = l_Lean_inferDefEqAttr(v___y_405_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_dec_ref(v___x_408_);
v___y_359_ = v___y_400_;
v___y_360_ = v___y_405_;
v___y_361_ = v___y_402_;
v___y_362_ = v___y_404_;
goto v___jp_358_;
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec(v___y_405_);
lean_dec_ref(v___y_400_);
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v___y_405_);
lean_dec_ref(v___y_400_);
v_a_417_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_407_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
v___jp_425_:
{
if (v___y_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_inc_n(v___y_431_, 2);
v___x_433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_433_, 0, v___y_431_);
lean_ctor_set(v___x_433_, 1, v_levelParams_339_);
lean_ctor_set(v___x_433_, 2, v_type_340_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___y_431_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_436_, 0, v___x_433_);
lean_ctor_set(v___x_436_, 1, v_value_341_);
lean_ctor_set(v___x_436_, 2, v___x_435_);
v___x_437_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
v___y_400_ = v___y_426_;
v___y_401_ = v___y_427_;
v___y_402_ = v___y_429_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_431_;
v___y_406_ = v___x_437_;
goto v___jp_399_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc_n(v___y_431_, 2);
v___x_438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_438_, 0, v___y_431_);
lean_ctor_set(v___x_438_, 1, v_levelParams_339_);
lean_ctor_set(v___x_438_, 2, v_type_340_);
v___x_439_ = lean_box(0);
v___x_440_ = 0;
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_442_, 0, v___y_431_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_443_, 0, v___x_438_);
lean_ctor_set(v___x_443_, 1, v_value_341_);
lean_ctor_set(v___x_443_, 2, v___x_439_);
lean_ctor_set(v___x_443_, 3, v___x_442_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*4, v___x_440_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
v___y_400_ = v___y_426_;
v___y_401_ = v___y_427_;
v___y_402_ = v___y_429_;
v___y_403_ = v___y_428_;
v___y_404_ = v___y_430_;
v___y_405_ = v___y_431_;
v___y_406_ = v___x_444_;
goto v___jp_399_;
}
}
v___jp_445_:
{
lean_object* v___x_452_; lean_object* v_a_453_; lean_object* v___f_454_; uint8_t v___x_455_; 
v___x_452_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_447_, v___y_451_);
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc_n(v_a_453_, 2);
lean_dec_ref(v___x_452_);
lean_inc(v_levelParams_339_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_454_, 0, v_a_453_);
lean_closure_set(v___f_454_, 1, v_levelParams_339_);
lean_closure_set(v___f_454_, 2, v___y_446_);
lean_inc_ref(v_env_352_);
v___x_455_ = l_Lean_Environment_hasUnsafe(v_env_352_, v_type_340_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_Environment_hasUnsafe(v_env_352_, v_value_341_);
v___y_426_ = v___f_454_;
v___y_427_ = v___y_448_;
v___y_428_ = v___y_450_;
v___y_429_ = v___y_449_;
v___y_430_ = v___y_451_;
v___y_431_ = v_a_453_;
v___y_432_ = v___x_456_;
goto v___jp_425_;
}
else
{
lean_dec_ref(v_env_352_);
v___y_426_ = v___f_454_;
v___y_427_ = v___y_448_;
v___y_428_ = v___y_450_;
v___y_429_ = v___y_449_;
v___y_430_ = v___y_451_;
v___y_431_ = v_a_453_;
v___y_432_ = v___x_455_;
goto v___jp_425_;
}
}
v___jp_457_:
{
lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_traceState_467_; lean_object* v_messages_468_; lean_object* v_infoState_469_; lean_object* v_snapshotTasks_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_496_; 
v___x_462_ = lean_st_ref_take(v___y_461_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
v_nextMacroScope_464_ = lean_ctor_get(v___x_462_, 1);
v_ngen_465_ = lean_ctor_get(v___x_462_, 2);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_462_, 3);
v_traceState_467_ = lean_ctor_get(v___x_462_, 4);
v_messages_468_ = lean_ctor_get(v___x_462_, 6);
v_infoState_469_ = lean_ctor_get(v___x_462_, 7);
v_snapshotTasks_470_ = lean_ctor_get(v___x_462_, 8);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v___x_462_, 5);
lean_dec(v_unused_497_);
v___x_472_ = v___x_462_;
v_isShared_473_ = v_isSharedCheck_496_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snapshotTasks_470_);
lean_inc(v_infoState_469_);
lean_inc(v_messages_468_);
lean_inc(v_traceState_467_);
lean_inc(v_auxDeclNGen_466_);
lean_inc(v_ngen_465_);
lean_inc(v_nextMacroScope_464_);
lean_inc(v_env_463_);
lean_dec(v___x_462_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_496_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = l_Lean_EnvExtension_modifyState___redArg(v___x_353_, v_env_463_, v___y_459_, v_asyncMode_354_, v___x_357_);
v___x_475_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__2, &l_Lean_Meta_mkAuxLemma___closed__2_once, _init_l_Lean_Meta_mkAuxLemma___closed__2);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 5, v___x_475_);
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_nextMacroScope_464_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_ngen_465_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_auxDeclNGen_466_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_traceState_467_);
lean_ctor_set(v_reuseFailAlloc_495_, 5, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_495_, 6, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_495_, 7, v_infoState_469_);
lean_ctor_set(v_reuseFailAlloc_495_, 8, v_snapshotTasks_470_);
v___x_477_ = v_reuseFailAlloc_495_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_mctx_480_; lean_object* v_zetaDeltaFVarIds_481_; lean_object* v_postponed_482_; lean_object* v_diag_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_493_; 
v___x_478_ = lean_st_ref_set(v___y_461_, v___x_477_);
v___x_479_ = lean_st_ref_take(v___y_460_);
v_mctx_480_ = lean_ctor_get(v___x_479_, 0);
v_zetaDeltaFVarIds_481_ = lean_ctor_get(v___x_479_, 2);
v_postponed_482_ = lean_ctor_get(v___x_479_, 3);
v_diag_483_ = lean_ctor_get(v___x_479_, 4);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v___x_479_, 1);
lean_dec(v_unused_494_);
v___x_485_ = v___x_479_;
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_diag_483_);
lean_inc(v_postponed_482_);
lean_inc(v_zetaDeltaFVarIds_481_);
lean_inc(v_mctx_480_);
lean_dec(v___x_479_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__3, &l_Lean_Meta_mkAuxLemma___closed__3_once, _init_l_Lean_Meta_mkAuxLemma___closed__3);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_487_);
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_mctx_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_zetaDeltaFVarIds_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_postponed_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_diag_483_);
v___x_489_ = v_reuseFailAlloc_492_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_st_ref_set(v___y_460_, v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___y_458_);
return v___x_491_;
}
}
}
}
}
v___jp_498_:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_addDecl(v___y_501_, v_forceExpose_345_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_dec_ref(v___x_502_);
if (v_inferRfl_344_ == 0)
{
v___y_458_ = v___y_499_;
v___y_459_ = v___y_500_;
v___y_460_ = v_a_347_;
v___y_461_ = v_a_349_;
goto v___jp_457_;
}
else
{
lean_object* v___x_503_; 
lean_inc(v___y_499_);
v___x_503_ = l_Lean_inferDefEqAttr(v___y_499_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_dec_ref(v___x_503_);
v___y_458_ = v___y_499_;
v___y_459_ = v___y_500_;
v___y_460_ = v_a_347_;
v___y_461_ = v_a_349_;
goto v___jp_457_;
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
v_a_512_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_502_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_502_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
v___jp_520_:
{
if (v___y_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_inc_n(v___y_521_, 2);
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v___y_521_);
lean_ctor_set(v___x_524_, 1, v_levelParams_339_);
lean_ctor_set(v___x_524_, 2, v_type_340_);
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_521_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v_value_341_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
v___x_528_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___y_499_ = v___y_521_;
v___y_500_ = v___y_522_;
v___y_501_ = v___x_528_;
goto v___jp_498_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
lean_inc_n(v___y_521_, 2);
v___x_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_529_, 0, v___y_521_);
lean_ctor_set(v___x_529_, 1, v_levelParams_339_);
lean_ctor_set(v___x_529_, 2, v_type_340_);
v___x_530_ = lean_box(0);
v___x_531_ = 0;
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_521_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_534_, 0, v___x_529_);
lean_ctor_set(v___x_534_, 1, v_value_341_);
lean_ctor_set(v___x_534_, 2, v___x_530_);
lean_ctor_set(v___x_534_, 3, v___x_533_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*4, v___x_531_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___y_499_ = v___y_521_;
v___y_500_ = v___y_522_;
v___y_501_ = v___x_535_;
goto v___jp_498_;
}
}
v___jp_537_:
{
if (v___y_539_ == 0)
{
lean_dec(v___x_536_);
v___y_446_ = v___y_538_;
v___y_447_ = v___y_540_;
v___y_448_ = v___y_541_;
v___y_449_ = v___y_542_;
v___y_450_ = v___y_543_;
v___y_451_ = v___y_544_;
goto v___jp_445_;
}
else
{
uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = 0;
lean_inc_ref(v_type_340_);
v___x_546_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_546_, 0, v_type_340_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*1, v___x_545_);
v___x_547_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v___x_536_, v___x_546_);
lean_dec_ref(v___x_546_);
lean_dec(v___x_536_);
if (lean_obj_tag(v___x_547_) == 1)
{
lean_object* v_val_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v_val_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_val_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_fst_552_; lean_object* v_snd_553_; uint8_t v___x_554_; 
v_fst_552_ = lean_ctor_get(v_val_548_, 0);
lean_inc(v_fst_552_);
v_snd_553_ = lean_ctor_get(v_val_548_, 1);
lean_inc(v_snd_553_);
lean_dec(v_val_548_);
v___x_554_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(v_levelParams_339_, v_snd_553_);
lean_dec(v_snd_553_);
if (v___x_554_ == 0)
{
lean_dec(v_fst_552_);
lean_del_object(v___x_550_);
v___y_446_ = v___y_538_;
v___y_447_ = v___y_540_;
v___y_448_ = v___y_541_;
v___y_449_ = v___y_542_;
v___y_450_ = v___y_543_;
v___y_451_ = v___y_544_;
goto v___jp_445_;
}
else
{
lean_object* v___x_556_; 
lean_dec(v___y_540_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_env_352_);
lean_dec_ref(v_value_341_);
lean_dec_ref(v_type_340_);
lean_dec(v_levelParams_339_);
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 0);
lean_ctor_set(v___x_550_, 0, v_fst_552_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_fst_552_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_dec(v___x_547_);
v___y_446_ = v___y_538_;
v___y_447_ = v___y_540_;
v___y_448_ = v___y_541_;
v___y_449_ = v___y_542_;
v___y_450_ = v___y_543_;
v___y_451_ = v___y_544_;
goto v___jp_445_;
}
}
}
v___jp_559_:
{
if (v_cache_343_ == 0)
{
lean_object* v___x_563_; lean_object* v_a_564_; lean_object* v___f_565_; uint8_t v___x_566_; 
lean_dec(v___x_536_);
v___x_563_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_562_, v_a_349_);
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_n(v_a_564_, 2);
lean_dec_ref(v___x_563_);
lean_inc(v_levelParams_339_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_565_, 0, v_a_564_);
lean_closure_set(v___f_565_, 1, v_levelParams_339_);
lean_closure_set(v___f_565_, 2, v___y_560_);
lean_inc_ref(v_env_352_);
v___x_566_ = l_Lean_Environment_hasUnsafe(v_env_352_, v_type_340_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Environment_hasUnsafe(v_env_352_, v_value_341_);
v___y_521_ = v_a_564_;
v___y_522_ = v___f_565_;
v___y_523_ = v___x_567_;
goto v___jp_520_;
}
else
{
lean_dec_ref(v_env_352_);
v___y_521_ = v_a_564_;
v___y_522_ = v___f_565_;
v___y_523_ = v___x_566_;
goto v___jp_520_;
}
}
else
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v___x_536_, v___y_560_);
if (lean_obj_tag(v___x_568_) == 1)
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_579_; 
v_val_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_579_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; uint8_t v___x_575_; 
v_fst_573_ = lean_ctor_get(v_val_569_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_val_569_, 1);
lean_inc(v_snd_574_);
lean_dec(v_val_569_);
v___x_575_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(v_levelParams_339_, v_snd_574_);
lean_dec(v_snd_574_);
if (v___x_575_ == 0)
{
lean_dec(v_fst_573_);
lean_del_object(v___x_571_);
v___y_538_ = v___y_560_;
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v_a_346_;
v___y_542_ = v_a_347_;
v___y_543_ = v_a_348_;
v___y_544_ = v_a_349_;
goto v___jp_537_;
}
else
{
lean_object* v___x_577_; 
lean_dec(v___y_562_);
lean_dec_ref(v___y_560_);
lean_dec(v___x_536_);
lean_dec_ref(v_env_352_);
lean_dec_ref(v_value_341_);
lean_dec_ref(v_type_340_);
lean_dec(v_levelParams_339_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 0);
lean_ctor_set(v___x_571_, 0, v_fst_573_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_fst_573_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_dec(v___x_568_);
v___y_538_ = v___y_560_;
v___y_539_ = v___y_561_;
v___y_540_ = v___y_562_;
v___y_541_ = v_a_346_;
v___y_542_ = v_a_347_;
v___y_543_ = v_a_348_;
v___y_544_ = v_a_349_;
goto v___jp_537_;
}
}
}
v___jp_580_:
{
lean_object* v___x_582_; 
lean_inc_ref(v_type_340_);
v___x_582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_582_, 0, v_type_340_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*1, v___y_581_);
if (lean_obj_tag(v_kind_x3f_342_) == 0)
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__5));
v___y_560_ = v___x_582_;
v___y_561_ = v___y_581_;
v___y_562_ = v___x_583_;
goto v___jp_559_;
}
else
{
lean_object* v_val_584_; 
v_val_584_ = lean_ctor_get(v_kind_x3f_342_, 0);
lean_inc(v_val_584_);
lean_dec_ref(v_kind_x3f_342_);
v___y_560_ = v___x_582_;
v___y_561_ = v___y_581_;
v___y_562_ = v_val_584_;
goto v___jp_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_587_, lean_object* v_type_588_, lean_object* v_value_589_, lean_object* v_kind_x3f_590_, lean_object* v_cache_591_, lean_object* v_inferRfl_592_, lean_object* v_forceExpose_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
uint8_t v_cache_boxed_599_; uint8_t v_inferRfl_boxed_600_; uint8_t v_forceExpose_boxed_601_; lean_object* v_res_602_; 
v_cache_boxed_599_ = lean_unbox(v_cache_591_);
v_inferRfl_boxed_600_ = lean_unbox(v_inferRfl_592_);
v_forceExpose_boxed_601_ = lean_unbox(v_forceExpose_593_);
v_res_602_ = l_Lean_Meta_mkAuxLemma(v_levelParams_587_, v_type_588_, v_value_589_, v_kind_x3f_590_, v_cache_boxed_599_, v_inferRfl_boxed_600_, v_forceExpose_boxed_601_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_604_, v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v_x_609_, v_x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2(v_00_u03b2_612_, v_x_613_, v_x_614_);
lean_dec_ref(v_x_614_);
lean_dec_ref(v_x_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_616_, lean_object* v_x_617_, size_t v_x_618_, size_t v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_617_, v_x_618_, v_x_619_, v_x_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
size_t v_x_4680__boxed_629_; size_t v_x_4681__boxed_630_; lean_object* v_res_631_; 
v_x_4680__boxed_629_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_x_4681__boxed_630_ = lean_unbox_usize(v_x_626_);
lean_dec(v_x_626_);
v_res_631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_623_, v_x_624_, v_x_4680__boxed_629_, v_x_4681__boxed_630_, v_x_627_, v_x_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_4697__boxed_641_; lean_object* v_res_642_; 
v_x_4697__boxed_641_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_642_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b2_637_, v_x_638_, v_x_4697__boxed_641_, v_x_640_);
lean_dec_ref(v_x_640_);
lean_dec_ref(v_x_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_643_, lean_object* v_n_644_, lean_object* v_k_645_, lean_object* v_v_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_644_, v_k_645_, v_v_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_648_, size_t v_depth_649_, lean_object* v_keys_650_, lean_object* v_vals_651_, lean_object* v_heq_652_, lean_object* v_i_653_, lean_object* v_entries_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_649_, v_keys_650_, v_vals_651_, v_i_653_, v_entries_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_656_, lean_object* v_depth_657_, lean_object* v_keys_658_, lean_object* v_vals_659_, lean_object* v_heq_660_, lean_object* v_i_661_, lean_object* v_entries_662_){
_start:
{
size_t v_depth_boxed_663_; lean_object* v_res_664_; 
v_depth_boxed_663_ = lean_unbox_usize(v_depth_657_);
lean_dec(v_depth_657_);
v_res_664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_656_, v_depth_boxed_663_, v_keys_658_, v_vals_659_, v_heq_660_, v_i_661_, v_entries_662_);
lean_dec_ref(v_vals_659_);
lean_dec_ref(v_keys_658_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_665_, lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_heq_668_, lean_object* v_i_669_, lean_object* v_k_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_keys_666_, v_vals_667_, v_i_669_, v_k_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_672_, lean_object* v_keys_673_, lean_object* v_vals_674_, lean_object* v_heq_675_, lean_object* v_i_676_, lean_object* v_k_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b2_672_, v_keys_673_, v_vals_674_, v_heq_675_, v_i_676_, v_k_677_);
lean_dec_ref(v_k_677_);
lean_dec_ref(v_vals_674_);
lean_dec_ref(v_keys_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5___redArg(v_x_680_, v_x_681_, v_x_682_, v_x_683_);
return v___x_684_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_DefEqAttrib(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedAuxLemmas_default = _init_l_Lean_Meta_instInhabitedAuxLemmas_default();
lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas_default);
l_Lean_Meta_instInhabitedAuxLemmas = _init_l_Lean_Meta_instInhabitedAuxLemmas();
lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas);
res = l___private_Lean_Meta_Tactic_AuxLemma_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_AuxLemma_830486828____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_auxLemmasExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_auxLemmasExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DefEqAttrib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_AuxLemma(builtin);
}
#ifdef __cplusplus
}
#endif
