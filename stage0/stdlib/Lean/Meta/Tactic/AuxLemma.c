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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
size_t v_x_3869__boxed_243_; size_t v_x_3870__boxed_244_; lean_object* v_res_245_; 
v_x_3869__boxed_243_ = lean_unbox_usize(v_x_239_);
lean_dec(v_x_239_);
v_x_3870__boxed_244_ = lean_unbox_usize(v_x_240_);
lean_dec(v_x_240_);
v_res_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_238_, v_x_3869__boxed_243_, v_x_3870__boxed_244_, v_x_241_, v_x_242_);
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
lean_object* v_es_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_302_; 
v_es_281_ = lean_ctor_get(v_x_278_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_302_ == 0)
{
v___x_283_ = v_x_278_;
v_isShared_284_ = v_isSharedCheck_302_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_es_281_);
lean_dec(v_x_278_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_302_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; lean_object* v_j_289_; lean_object* v___x_290_; 
v___x_285_ = lean_box(2);
v___x_286_ = ((size_t)5ULL);
v___x_287_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg___closed__1);
v___x_288_ = lean_usize_land(v_x_279_, v___x_287_);
v_j_289_ = lean_usize_to_nat(v___x_288_);
v___x_290_ = lean_array_get(v___x_285_, v_es_281_, v_j_289_);
lean_dec(v_j_289_);
lean_dec_ref(v_es_281_);
switch(lean_obj_tag(v___x_290_))
{
case 0:
{
lean_object* v_key_291_; lean_object* v_val_292_; uint8_t v___x_293_; 
v_key_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_key_291_);
v_val_292_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_val_292_);
lean_dec_ref(v___x_290_);
v___x_293_ = l_Lean_Meta_instBEqAuxLemmaKey_beq(v_x_280_, v_key_291_);
lean_dec(v_key_291_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
lean_dec(v_val_292_);
lean_del_object(v___x_283_);
v___x_294_ = lean_box(0);
return v___x_294_;
}
else
{
lean_object* v___x_296_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
lean_ctor_set(v___x_283_, 0, v_val_292_);
v___x_296_ = v___x_283_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_val_292_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
case 1:
{
lean_object* v_node_298_; size_t v___x_299_; 
lean_del_object(v___x_283_);
v_node_298_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_node_298_);
lean_dec_ref(v___x_290_);
v___x_299_ = lean_usize_shift_right(v_x_279_, v___x_286_);
v_x_278_ = v_node_298_;
v_x_279_ = v___x_299_;
goto _start;
}
default: 
{
lean_object* v___x_301_; 
lean_del_object(v___x_283_);
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
}
}
else
{
lean_object* v_ks_303_; lean_object* v_vs_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_ks_303_ = lean_ctor_get(v_x_278_, 0);
lean_inc_ref(v_ks_303_);
v_vs_304_ = lean_ctor_get(v_x_278_, 1);
lean_inc_ref(v_vs_304_);
lean_dec_ref(v_x_278_);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_ks_303_, v_vs_304_, v___x_305_, v_x_280_);
lean_dec_ref(v_vs_304_);
lean_dec_ref(v_ks_303_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
size_t v_x_4079__boxed_310_; lean_object* v_res_311_; 
v_x_4079__boxed_310_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_res_311_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_x_307_, v_x_4079__boxed_310_, v_x_309_);
lean_dec_ref(v_x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint64_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_Meta_instHashableAuxLemmaKey_hash(v_x_313_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_x_312_, v___x_315_, v_x_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v_x_317_, v_x_318_);
lean_dec_ref(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
if (lean_obj_tag(v_x_321_) == 0)
{
uint8_t v___x_322_; 
v___x_322_ = 1;
return v___x_322_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = 0;
return v___x_323_;
}
}
else
{
if (lean_obj_tag(v_x_321_) == 0)
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
else
{
lean_object* v_head_325_; lean_object* v_tail_326_; lean_object* v_head_327_; lean_object* v_tail_328_; uint8_t v___x_329_; 
v_head_325_ = lean_ctor_get(v_x_320_, 0);
v_tail_326_ = lean_ctor_get(v_x_320_, 1);
v_head_327_ = lean_ctor_get(v_x_321_, 0);
v_tail_328_ = lean_ctor_get(v_x_321_, 1);
v___x_329_ = lean_name_eq(v_head_325_, v_head_327_);
if (v___x_329_ == 0)
{
return v___x_329_;
}
else
{
v_x_320_ = v_tail_326_;
v_x_321_ = v_tail_328_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
lean_dec(v_x_331_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__0, &l_Lean_Meta_mkAuxLemma___closed__0_once, _init_l_Lean_Meta_mkAuxLemma___closed__0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__1, &l_Lean_Meta_mkAuxLemma___closed__1_once, _init_l_Lean_Meta_mkAuxLemma___closed__1);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__1, &l_Lean_Meta_mkAuxLemma___closed__1_once, _init_l_Lean_Meta_mkAuxLemma___closed__1);
v___x_341_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
lean_ctor_set(v___x_341_, 3, v___x_340_);
lean_ctor_set(v___x_341_, 4, v___x_340_);
lean_ctor_set(v___x_341_, 5, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma(lean_object* v_levelParams_345_, lean_object* v_type_346_, lean_object* v_value_347_, lean_object* v_kind_x3f_348_, uint8_t v_cache_349_, uint8_t v_inferRfl_350_, uint8_t v_forceExpose_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_env_358_; lean_object* v___x_359_; lean_object* v_asyncMode_360_; uint8_t v_isExporting_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___x_542_; lean_object* v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; uint8_t v___y_587_; 
v___x_357_ = lean_st_ref_get(v_a_355_);
v_env_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref_n(v_env_358_, 2);
lean_dec(v___x_357_);
v___x_359_ = l_Lean_Meta_auxLemmasExt;
v_asyncMode_360_ = lean_ctor_get(v___x_359_, 2);
v_isExporting_361_ = lean_ctor_get_uint8(v_env_358_, sizeof(void*)*8);
v___x_362_ = l_Lean_Meta_instInhabitedAuxLemmas_default;
v___x_363_ = lean_box(0);
v___x_542_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_362_, v___x_359_, v_env_358_, v_asyncMode_360_, v___x_363_);
if (v_isExporting_361_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = 1;
v___y_587_ = v___x_591_;
goto v___jp_586_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = 0;
v___y_587_ = v___x_592_;
goto v___jp_586_;
}
v___jp_364_:
{
lean_object* v___x_369_; lean_object* v_env_370_; lean_object* v_nextMacroScope_371_; lean_object* v_ngen_372_; lean_object* v_auxDeclNGen_373_; lean_object* v_traceState_374_; lean_object* v_messages_375_; lean_object* v_infoState_376_; lean_object* v_snapshotTasks_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_403_; 
v___x_369_ = lean_st_ref_take(v___y_368_);
v_env_370_ = lean_ctor_get(v___x_369_, 0);
v_nextMacroScope_371_ = lean_ctor_get(v___x_369_, 1);
v_ngen_372_ = lean_ctor_get(v___x_369_, 2);
v_auxDeclNGen_373_ = lean_ctor_get(v___x_369_, 3);
v_traceState_374_ = lean_ctor_get(v___x_369_, 4);
v_messages_375_ = lean_ctor_get(v___x_369_, 6);
v_infoState_376_ = lean_ctor_get(v___x_369_, 7);
v_snapshotTasks_377_ = lean_ctor_get(v___x_369_, 8);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_369_, 5);
lean_dec(v_unused_404_);
v___x_379_ = v___x_369_;
v_isShared_380_ = v_isSharedCheck_403_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_snapshotTasks_377_);
lean_inc(v_infoState_376_);
lean_inc(v_messages_375_);
lean_inc(v_traceState_374_);
lean_inc(v_auxDeclNGen_373_);
lean_inc(v_ngen_372_);
lean_inc(v_nextMacroScope_371_);
lean_inc(v_env_370_);
lean_dec(v___x_369_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_403_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = l_Lean_EnvExtension_modifyState___redArg(v___x_359_, v_env_370_, v___y_366_, v_asyncMode_360_, v___x_363_);
v___x_382_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__2, &l_Lean_Meta_mkAuxLemma___closed__2_once, _init_l_Lean_Meta_mkAuxLemma___closed__2);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 5, v___x_382_);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_384_ = v___x_379_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_nextMacroScope_371_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_ngen_372_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_auxDeclNGen_373_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_traceState_374_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_messages_375_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v_infoState_376_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_snapshotTasks_377_);
v___x_384_ = v_reuseFailAlloc_402_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_mctx_387_; lean_object* v_zetaDeltaFVarIds_388_; lean_object* v_postponed_389_; lean_object* v_diag_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_400_; 
v___x_385_ = lean_st_ref_set(v___y_368_, v___x_384_);
v___x_386_ = lean_st_ref_take(v___y_367_);
v_mctx_387_ = lean_ctor_get(v___x_386_, 0);
v_zetaDeltaFVarIds_388_ = lean_ctor_get(v___x_386_, 2);
v_postponed_389_ = lean_ctor_get(v___x_386_, 3);
v_diag_390_ = lean_ctor_get(v___x_386_, 4);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v___x_386_, 1);
lean_dec(v_unused_401_);
v___x_392_ = v___x_386_;
v_isShared_393_ = v_isSharedCheck_400_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_diag_390_);
lean_inc(v_postponed_389_);
lean_inc(v_zetaDeltaFVarIds_388_);
lean_inc(v_mctx_387_);
lean_dec(v___x_386_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_400_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__3, &l_Lean_Meta_mkAuxLemma___closed__3_once, _init_l_Lean_Meta_mkAuxLemma___closed__3);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_mctx_387_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_zetaDeltaFVarIds_388_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_postponed_389_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_diag_390_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_st_ref_set(v___y_367_, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___y_365_);
return v___x_398_;
}
}
}
}
}
v___jp_405_:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_addDecl(v___y_412_, v_forceExpose_351_, v___y_406_, v___y_409_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_dec_ref(v___x_413_);
if (v_inferRfl_350_ == 0)
{
v___y_365_ = v___y_411_;
v___y_366_ = v___y_410_;
v___y_367_ = v___y_407_;
v___y_368_ = v___y_409_;
goto v___jp_364_;
}
else
{
lean_object* v___x_414_; 
lean_inc(v___y_411_);
v___x_414_ = l_Lean_inferDefEqAttr(v___y_411_, v___y_408_, v___y_407_, v___y_406_, v___y_409_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_dec_ref(v___x_414_);
v___y_365_ = v___y_411_;
v___y_366_ = v___y_410_;
v___y_367_ = v___y_407_;
v___y_368_ = v___y_409_;
goto v___jp_364_;
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
v_a_423_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_413_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_413_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
v___jp_431_:
{
if (v___y_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_inc_n(v___y_436_, 2);
v___x_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_439_, 0, v___y_436_);
lean_ctor_set(v___x_439_, 1, v_levelParams_345_);
lean_ctor_set(v___x_439_, 2, v_type_346_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v___y_436_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_439_);
lean_ctor_set(v___x_442_, 1, v_value_347_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
v___x_443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
v___y_406_ = v___y_432_;
v___y_407_ = v___y_433_;
v___y_408_ = v___y_434_;
v___y_409_ = v___y_435_;
v___y_410_ = v___y_437_;
v___y_411_ = v___y_436_;
v___y_412_ = v___x_443_;
goto v___jp_405_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc_n(v___y_436_, 2);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v___y_436_);
lean_ctor_set(v___x_444_, 1, v_levelParams_345_);
lean_ctor_set(v___x_444_, 2, v_type_346_);
v___x_445_ = lean_box(0);
v___x_446_ = 0;
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___y_436_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_449_, 0, v___x_444_);
lean_ctor_set(v___x_449_, 1, v_value_347_);
lean_ctor_set(v___x_449_, 2, v___x_445_);
lean_ctor_set(v___x_449_, 3, v___x_448_);
lean_ctor_set_uint8(v___x_449_, sizeof(void*)*4, v___x_446_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
v___y_406_ = v___y_432_;
v___y_407_ = v___y_433_;
v___y_408_ = v___y_434_;
v___y_409_ = v___y_435_;
v___y_410_ = v___y_437_;
v___y_411_ = v___y_436_;
v___y_412_ = v___x_450_;
goto v___jp_405_;
}
}
v___jp_451_:
{
lean_object* v___x_458_; lean_object* v_a_459_; lean_object* v___f_460_; uint8_t v___x_461_; 
v___x_458_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_453_, v___y_457_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_n(v_a_459_, 2);
lean_dec_ref(v___x_458_);
lean_inc(v_levelParams_345_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_460_, 0, v_a_459_);
lean_closure_set(v___f_460_, 1, v_levelParams_345_);
lean_closure_set(v___f_460_, 2, v___y_452_);
lean_inc_ref(v_env_358_);
v___x_461_ = l_Lean_Environment_hasUnsafe(v_env_358_, v_type_346_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_Environment_hasUnsafe(v_env_358_, v_value_347_);
v___y_432_ = v___y_456_;
v___y_433_ = v___y_455_;
v___y_434_ = v___y_454_;
v___y_435_ = v___y_457_;
v___y_436_ = v_a_459_;
v___y_437_ = v___f_460_;
v___y_438_ = v___x_462_;
goto v___jp_431_;
}
else
{
lean_dec_ref(v_env_358_);
v___y_432_ = v___y_456_;
v___y_433_ = v___y_455_;
v___y_434_ = v___y_454_;
v___y_435_ = v___y_457_;
v___y_436_ = v_a_459_;
v___y_437_ = v___f_460_;
v___y_438_ = v___x_461_;
goto v___jp_431_;
}
}
v___jp_463_:
{
lean_object* v___x_468_; lean_object* v_env_469_; lean_object* v_nextMacroScope_470_; lean_object* v_ngen_471_; lean_object* v_auxDeclNGen_472_; lean_object* v_traceState_473_; lean_object* v_messages_474_; lean_object* v_infoState_475_; lean_object* v_snapshotTasks_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_502_; 
v___x_468_ = lean_st_ref_take(v___y_467_);
v_env_469_ = lean_ctor_get(v___x_468_, 0);
v_nextMacroScope_470_ = lean_ctor_get(v___x_468_, 1);
v_ngen_471_ = lean_ctor_get(v___x_468_, 2);
v_auxDeclNGen_472_ = lean_ctor_get(v___x_468_, 3);
v_traceState_473_ = lean_ctor_get(v___x_468_, 4);
v_messages_474_ = lean_ctor_get(v___x_468_, 6);
v_infoState_475_ = lean_ctor_get(v___x_468_, 7);
v_snapshotTasks_476_ = lean_ctor_get(v___x_468_, 8);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_468_, 5);
lean_dec(v_unused_503_);
v___x_478_ = v___x_468_;
v_isShared_479_ = v_isSharedCheck_502_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snapshotTasks_476_);
lean_inc(v_infoState_475_);
lean_inc(v_messages_474_);
lean_inc(v_traceState_473_);
lean_inc(v_auxDeclNGen_472_);
lean_inc(v_ngen_471_);
lean_inc(v_nextMacroScope_470_);
lean_inc(v_env_469_);
lean_dec(v___x_468_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_502_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_480_ = l_Lean_EnvExtension_modifyState___redArg(v___x_359_, v_env_469_, v___y_465_, v_asyncMode_360_, v___x_363_);
v___x_481_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__2, &l_Lean_Meta_mkAuxLemma___closed__2_once, _init_l_Lean_Meta_mkAuxLemma___closed__2);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 5, v___x_481_);
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_nextMacroScope_470_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_ngen_471_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_auxDeclNGen_472_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_traceState_473_);
lean_ctor_set(v_reuseFailAlloc_501_, 5, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_501_, 6, v_messages_474_);
lean_ctor_set(v_reuseFailAlloc_501_, 7, v_infoState_475_);
lean_ctor_set(v_reuseFailAlloc_501_, 8, v_snapshotTasks_476_);
v___x_483_ = v_reuseFailAlloc_501_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_mctx_486_; lean_object* v_zetaDeltaFVarIds_487_; lean_object* v_postponed_488_; lean_object* v_diag_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_499_; 
v___x_484_ = lean_st_ref_set(v___y_467_, v___x_483_);
v___x_485_ = lean_st_ref_take(v___y_466_);
v_mctx_486_ = lean_ctor_get(v___x_485_, 0);
v_zetaDeltaFVarIds_487_ = lean_ctor_get(v___x_485_, 2);
v_postponed_488_ = lean_ctor_get(v___x_485_, 3);
v_diag_489_ = lean_ctor_get(v___x_485_, 4);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_485_, 1);
lean_dec(v_unused_500_);
v___x_491_ = v___x_485_;
v_isShared_492_ = v_isSharedCheck_499_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_diag_489_);
lean_inc(v_postponed_488_);
lean_inc(v_zetaDeltaFVarIds_487_);
lean_inc(v_mctx_486_);
lean_dec(v___x_485_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_499_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_obj_once(&l_Lean_Meta_mkAuxLemma___closed__3, &l_Lean_Meta_mkAuxLemma___closed__3_once, _init_l_Lean_Meta_mkAuxLemma___closed__3);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_mctx_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_zetaDeltaFVarIds_487_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_postponed_488_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_diag_489_);
v___x_495_ = v_reuseFailAlloc_498_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_st_ref_set(v___y_466_, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___y_464_);
return v___x_497_;
}
}
}
}
}
v___jp_504_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_addDecl(v___y_507_, v_forceExpose_351_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_dec_ref(v___x_508_);
if (v_inferRfl_350_ == 0)
{
v___y_464_ = v___y_505_;
v___y_465_ = v___y_506_;
v___y_466_ = v_a_353_;
v___y_467_ = v_a_355_;
goto v___jp_463_;
}
else
{
lean_object* v___x_509_; 
lean_inc(v___y_505_);
v___x_509_ = l_Lean_inferDefEqAttr(v___y_505_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_dec_ref(v___x_509_);
v___y_464_ = v___y_505_;
v___y_465_ = v___y_506_;
v___y_466_ = v_a_353_;
v___y_467_ = v_a_355_;
goto v___jp_463_;
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
v_a_518_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_508_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_508_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
v___jp_526_:
{
if (v___y_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_inc_n(v___y_527_, 2);
v___x_530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_530_, 0, v___y_527_);
lean_ctor_set(v___x_530_, 1, v_levelParams_345_);
lean_ctor_set(v___x_530_, 2, v_type_346_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_527_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v_value_347_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
v___y_505_ = v___y_527_;
v___y_506_ = v___y_528_;
v___y_507_ = v___x_534_;
goto v___jp_504_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_inc_n(v___y_527_, 2);
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v___y_527_);
lean_ctor_set(v___x_535_, 1, v_levelParams_345_);
lean_ctor_set(v___x_535_, 2, v_type_346_);
v___x_536_ = lean_box(0);
v___x_537_ = 0;
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_539_, 0, v___y_527_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_540_, 0, v___x_535_);
lean_ctor_set(v___x_540_, 1, v_value_347_);
lean_ctor_set(v___x_540_, 2, v___x_536_);
lean_ctor_set(v___x_540_, 3, v___x_539_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*4, v___x_537_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
v___y_505_ = v___y_527_;
v___y_506_ = v___y_528_;
v___y_507_ = v___x_541_;
goto v___jp_504_;
}
}
v___jp_543_:
{
if (v___y_546_ == 0)
{
lean_dec(v___x_542_);
v___y_452_ = v___y_544_;
v___y_453_ = v___y_545_;
v___y_454_ = v___y_547_;
v___y_455_ = v___y_548_;
v___y_456_ = v___y_549_;
v___y_457_ = v___y_550_;
goto v___jp_451_;
}
else
{
uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = 0;
lean_inc_ref(v_type_346_);
v___x_552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_552_, 0, v_type_346_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*1, v___x_551_);
v___x_553_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v___x_542_, v___x_552_);
lean_dec_ref(v___x_552_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_564_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_564_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; uint8_t v___x_560_; 
v_fst_558_ = lean_ctor_get(v_val_554_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_val_554_, 1);
lean_inc(v_snd_559_);
lean_dec(v_val_554_);
v___x_560_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(v_levelParams_345_, v_snd_559_);
lean_dec(v_snd_559_);
if (v___x_560_ == 0)
{
lean_dec(v_fst_558_);
lean_del_object(v___x_556_);
v___y_452_ = v___y_544_;
v___y_453_ = v___y_545_;
v___y_454_ = v___y_547_;
v___y_455_ = v___y_548_;
v___y_456_ = v___y_549_;
v___y_457_ = v___y_550_;
goto v___jp_451_;
}
else
{
lean_object* v___x_562_; 
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_env_358_);
lean_dec_ref(v_value_347_);
lean_dec_ref(v_type_346_);
lean_dec(v_levelParams_345_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
lean_ctor_set(v___x_556_, 0, v_fst_558_);
v___x_562_ = v___x_556_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_fst_558_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_dec(v___x_553_);
v___y_452_ = v___y_544_;
v___y_453_ = v___y_545_;
v___y_454_ = v___y_547_;
v___y_455_ = v___y_548_;
v___y_456_ = v___y_549_;
v___y_457_ = v___y_550_;
goto v___jp_451_;
}
}
}
v___jp_565_:
{
if (v_cache_349_ == 0)
{
lean_object* v___x_569_; lean_object* v_a_570_; lean_object* v___f_571_; uint8_t v___x_572_; 
lean_dec(v___x_542_);
v___x_569_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkAuxLemma_spec__0___redArg(v___y_568_, v_a_355_);
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_n(v_a_570_, 2);
lean_dec_ref(v___x_569_);
lean_inc(v_levelParams_345_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lam__0), 4, 3);
lean_closure_set(v___f_571_, 0, v_a_570_);
lean_closure_set(v___f_571_, 1, v_levelParams_345_);
lean_closure_set(v___f_571_, 2, v___y_566_);
lean_inc_ref(v_env_358_);
v___x_572_ = l_Lean_Environment_hasUnsafe(v_env_358_, v_type_346_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_Environment_hasUnsafe(v_env_358_, v_value_347_);
v___y_527_ = v_a_570_;
v___y_528_ = v___f_571_;
v___y_529_ = v___x_573_;
goto v___jp_526_;
}
else
{
lean_dec_ref(v_env_358_);
v___y_527_ = v_a_570_;
v___y_528_ = v___f_571_;
v___y_529_ = v___x_572_;
goto v___jp_526_;
}
}
else
{
lean_object* v___x_574_; 
lean_inc(v___x_542_);
v___x_574_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v___x_542_, v___y_566_);
if (lean_obj_tag(v___x_574_) == 1)
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_val_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_fst_579_; lean_object* v_snd_580_; uint8_t v___x_581_; 
v_fst_579_ = lean_ctor_get(v_val_575_, 0);
lean_inc(v_fst_579_);
v_snd_580_ = lean_ctor_get(v_val_575_, 1);
lean_inc(v_snd_580_);
lean_dec(v_val_575_);
v___x_581_ = l_List_beq___at___00Lean_Meta_mkAuxLemma_spec__3(v_levelParams_345_, v_snd_580_);
lean_dec(v_snd_580_);
if (v___x_581_ == 0)
{
lean_dec(v_fst_579_);
lean_del_object(v___x_577_);
v___y_544_ = v___y_566_;
v___y_545_ = v___y_568_;
v___y_546_ = v___y_567_;
v___y_547_ = v_a_352_;
v___y_548_ = v_a_353_;
v___y_549_ = v_a_354_;
v___y_550_ = v_a_355_;
goto v___jp_543_;
}
else
{
lean_object* v___x_583_; 
lean_dec(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec(v___x_542_);
lean_dec_ref(v_env_358_);
lean_dec_ref(v_value_347_);
lean_dec_ref(v_type_346_);
lean_dec(v_levelParams_345_);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
lean_ctor_set(v___x_577_, 0, v_fst_579_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_fst_579_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_dec(v___x_574_);
v___y_544_ = v___y_566_;
v___y_545_ = v___y_568_;
v___y_546_ = v___y_567_;
v___y_547_ = v_a_352_;
v___y_548_ = v_a_353_;
v___y_549_ = v_a_354_;
v___y_550_ = v_a_355_;
goto v___jp_543_;
}
}
}
v___jp_586_:
{
lean_object* v___x_588_; 
lean_inc_ref(v_type_346_);
v___x_588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_588_, 0, v_type_346_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*1, v___y_587_);
if (lean_obj_tag(v_kind_x3f_348_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_mkAuxLemma___closed__5));
v___y_566_ = v___x_588_;
v___y_567_ = v___y_587_;
v___y_568_ = v___x_589_;
goto v___jp_565_;
}
else
{
lean_object* v_val_590_; 
v_val_590_ = lean_ctor_get(v_kind_x3f_348_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v_kind_x3f_348_);
v___y_566_ = v___x_588_;
v___y_567_ = v___y_587_;
v___y_568_ = v_val_590_;
goto v___jp_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* v_levelParams_593_, lean_object* v_type_594_, lean_object* v_value_595_, lean_object* v_kind_x3f_596_, lean_object* v_cache_597_, lean_object* v_inferRfl_598_, lean_object* v_forceExpose_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_cache_boxed_605_; uint8_t v_inferRfl_boxed_606_; uint8_t v_forceExpose_boxed_607_; lean_object* v_res_608_; 
v_cache_boxed_605_ = lean_unbox(v_cache_597_);
v_inferRfl_boxed_606_ = lean_unbox(v_inferRfl_598_);
v_forceExpose_boxed_607_ = lean_unbox(v_forceExpose_599_);
v_res_608_ = l_Lean_Meta_mkAuxLemma(v_levelParams_593_, v_type_594_, v_value_595_, v_kind_x3f_596_, v_cache_boxed_605_, v_inferRfl_boxed_606_, v_forceExpose_boxed_607_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1___redArg(v_x_610_, v_x_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___redArg(v_x_615_, v_x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2___boxed(lean_object* v_00_u03b2_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2(v_00_u03b2_618_, v_x_619_, v_x_620_);
lean_dec_ref(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, size_t v_x_624_, size_t v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___redArg(v_x_623_, v_x_624_, v_x_625_, v_x_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1___boxed(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
size_t v_x_4678__boxed_635_; size_t v_x_4679__boxed_636_; lean_object* v_res_637_; 
v_x_4678__boxed_635_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_x_4679__boxed_636_ = lean_unbox_usize(v_x_632_);
lean_dec(v_x_632_);
v_res_637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1(v_00_u03b2_629_, v_x_630_, v_x_4678__boxed_635_, v_x_4679__boxed_636_, v_x_633_, v_x_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, size_t v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___redArg(v_x_639_, v_x_640_, v_x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
size_t v_x_4695__boxed_647_; lean_object* v_res_648_; 
v_x_4695__boxed_647_ = lean_unbox_usize(v_x_645_);
lean_dec(v_x_645_);
v_res_648_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3(v_00_u03b2_643_, v_x_644_, v_x_4695__boxed_647_, v_x_646_);
lean_dec_ref(v_x_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_649_, lean_object* v_n_650_, lean_object* v_k_651_, lean_object* v_v_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2___redArg(v_n_650_, v_k_651_, v_v_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_654_, size_t v_depth_655_, lean_object* v_keys_656_, lean_object* v_vals_657_, lean_object* v_heq_658_, lean_object* v_i_659_, lean_object* v_entries_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___redArg(v_depth_655_, v_keys_656_, v_vals_657_, v_i_659_, v_entries_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_662_, lean_object* v_depth_663_, lean_object* v_keys_664_, lean_object* v_vals_665_, lean_object* v_heq_666_, lean_object* v_i_667_, lean_object* v_entries_668_){
_start:
{
size_t v_depth_boxed_669_; lean_object* v_res_670_; 
v_depth_boxed_669_ = lean_unbox_usize(v_depth_663_);
lean_dec(v_depth_663_);
v_res_670_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__3(v_00_u03b2_662_, v_depth_boxed_669_, v_keys_664_, v_vals_665_, v_heq_666_, v_i_667_, v_entries_668_);
lean_dec_ref(v_vals_665_);
lean_dec_ref(v_keys_664_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_671_, lean_object* v_keys_672_, lean_object* v_vals_673_, lean_object* v_heq_674_, lean_object* v_i_675_, lean_object* v_k_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___redArg(v_keys_672_, v_vals_673_, v_i_675_, v_k_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_678_, lean_object* v_keys_679_, lean_object* v_vals_680_, lean_object* v_heq_681_, lean_object* v_i_682_, lean_object* v_k_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkAuxLemma_spec__2_spec__3_spec__6(v_00_u03b2_678_, v_keys_679_, v_vals_680_, v_heq_681_, v_i_682_, v_k_683_);
lean_dec_ref(v_k_683_);
lean_dec_ref(v_vals_680_);
lean_dec_ref(v_keys_679_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkAuxLemma_spec__1_spec__1_spec__2_spec__5___redArg(v_x_686_, v_x_687_, v_x_688_, v_x_689_);
return v___x_690_;
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
