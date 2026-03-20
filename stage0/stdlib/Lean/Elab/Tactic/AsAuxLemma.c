// Lean compiler output
// Module: Lean.Elab.Tactic.AsAuxLemma
// Imports: public import Lean.Elab.Tactic.Meta
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabAsAuxLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Cannot abstract term into auxiliary lemma because there are open goals."};
static const lean_object* l_elabAsAuxLemma___lam__0___closed__0 = (const lean_object*)&l_elabAsAuxLemma___lam__0___closed__0_value;
static lean_once_cell_t l_elabAsAuxLemma___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabAsAuxLemma___lam__0___closed__1;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabAsAuxLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_elabAsAuxLemma___closed__0 = (const lean_object*)&l_elabAsAuxLemma___closed__0_value;
static const lean_string_object l_elabAsAuxLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_elabAsAuxLemma___closed__1 = (const lean_object*)&l_elabAsAuxLemma___closed__1_value;
static const lean_string_object l_elabAsAuxLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_elabAsAuxLemma___closed__2 = (const lean_object*)&l_elabAsAuxLemma___closed__2_value;
static const lean_string_object l_elabAsAuxLemma___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "as_aux_lemma"};
static const lean_object* l_elabAsAuxLemma___closed__3 = (const lean_object*)&l_elabAsAuxLemma___closed__3_value;
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabAsAuxLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabAsAuxLemma___closed__4_value_aux_0),((lean_object*)&l_elabAsAuxLemma___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabAsAuxLemma___closed__4_value_aux_1),((lean_object*)&l_elabAsAuxLemma___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_elabAsAuxLemma___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabAsAuxLemma___closed__4_value_aux_2),((lean_object*)&l_elabAsAuxLemma___closed__3_value),LEAN_SCALAR_PTR_LITERAL(248, 107, 244, 71, 211, 100, 179, 147)}};
static const lean_object* l_elabAsAuxLemma___closed__4 = (const lean_object*)&l_elabAsAuxLemma___closed__4_value;
static const lean_string_object l_elabAsAuxLemma___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Invalid as_aux_lemma syntax"};
static const lean_object* l_elabAsAuxLemma___closed__5 = (const lean_object*)&l_elabAsAuxLemma___closed__5_value;
static lean_once_cell_t l_elabAsAuxLemma___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabAsAuxLemma___closed__6;
LEAN_EXPORT lean_object* l_elabAsAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabAsAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabAsAuxLemma"};
static const lean_object* l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0 = (const lean_object*)&l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value;
static const lean_ctor_object l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 189, 57, 147, 172, 30, 246, 215)}};
static const lean_object* l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1 = (const lean_object*)&l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
LEAN_EXPORT lean_object* l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_30_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_ks_56_; lean_object* v_vs_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_81_; 
v_ks_56_ = lean_ctor_get(v_x_52_, 0);
v_vs_57_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_81_ == 0)
{
v___x_59_ = v_x_52_;
v_isShared_60_ = v_isSharedCheck_81_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_vs_57_);
lean_inc(v_ks_56_);
lean_dec(v_x_52_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_81_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_array_get_size(v_ks_56_);
v___x_62_ = lean_nat_dec_lt(v_x_53_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
lean_dec(v_x_53_);
v___x_63_ = lean_array_push(v_ks_56_, v_x_54_);
v___x_64_ = lean_array_push(v_vs_57_, v_x_55_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_64_);
lean_ctor_set(v___x_59_, 0, v___x_63_);
v___x_66_ = v___x_59_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_object* v_k_x27_68_; uint8_t v___x_69_; 
v_k_x27_68_ = lean_array_fget_borrowed(v_ks_56_, v_x_53_);
v___x_69_ = l_Lean_instBEqMVarId_beq(v_x_54_, v_k_x27_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_71_; 
if (v_isShared_60_ == 0)
{
v___x_71_ = v___x_59_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_ks_56_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_vs_57_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_x_53_, v___x_72_);
lean_dec(v_x_53_);
v_x_52_ = v___x_71_;
v_x_53_ = v___x_73_;
goto _start;
}
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_76_ = lean_array_fset(v_ks_56_, v_x_53_, v_x_54_);
v___x_77_ = lean_array_fset(v_vs_57_, v_x_53_, v_x_55_);
lean_dec(v_x_53_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_77_);
lean_ctor_set(v___x_59_, 0, v___x_76_);
v___x_79_ = v___x_59_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_82_, lean_object* v_k_83_, lean_object* v_v_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_82_, v___x_85_, v_k_83_, v_v_84_);
return v___x_86_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; 
v___x_87_ = ((size_t)5ULL);
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_shift_left(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; 
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_92_ = lean_usize_sub(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object* v_x_94_, size_t v_x_95_, size_t v_x_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v_es_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v_j_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_es_99_ = lean_ctor_get(v_x_94_, 0);
v___x_100_ = ((size_t)5ULL);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_103_ = lean_usize_land(v_x_95_, v___x_102_);
v_j_104_ = lean_usize_to_nat(v___x_103_);
v___x_105_ = lean_array_get_size(v_es_99_);
v___x_106_ = lean_nat_dec_lt(v_j_104_, v___x_105_);
if (v___x_106_ == 0)
{
lean_dec(v_j_104_);
lean_dec(v_x_98_);
lean_dec(v_x_97_);
return v_x_94_;
}
else
{
lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_143_; 
lean_inc_ref(v_es_99_);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v_x_94_, 0);
lean_dec(v_unused_144_);
v___x_108_ = v_x_94_;
v_isShared_109_ = v_isSharedCheck_143_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_x_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_143_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_v_110_; lean_object* v___x_111_; lean_object* v_xs_x27_112_; lean_object* v___y_114_; 
v_v_110_ = lean_array_fget(v_es_99_, v_j_104_);
v___x_111_ = lean_box(0);
v_xs_x27_112_ = lean_array_fset(v_es_99_, v_j_104_, v___x_111_);
switch(lean_obj_tag(v_v_110_))
{
case 0:
{
lean_object* v_key_119_; lean_object* v_val_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_key_119_ = lean_ctor_get(v_v_110_, 0);
v_val_120_ = lean_ctor_get(v_v_110_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_v_110_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_v_110_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_val_120_);
lean_inc(v_key_119_);
lean_dec(v_v_110_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint8_t v___x_124_; 
v___x_124_ = l_Lean_instBEqMVarId_beq(v_x_97_, v_key_119_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_del_object(v___x_122_);
v___x_125_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_119_, v_val_120_, v_x_97_, v_x_98_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___y_114_ = v___x_126_;
goto v___jp_113_;
}
else
{
lean_object* v___x_128_; 
lean_dec(v_val_120_);
lean_dec(v_key_119_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_x_98_);
lean_ctor_set(v___x_122_, 0, v_x_97_);
v___x_128_ = v___x_122_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_x_97_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_x_98_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v___y_114_ = v___x_128_;
goto v___jp_113_;
}
}
}
}
case 1:
{
lean_object* v_node_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_141_; 
v_node_131_ = lean_ctor_get(v_v_110_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_v_110_);
if (v_isSharedCheck_141_ == 0)
{
v___x_133_ = v_v_110_;
v_isShared_134_ = v_isSharedCheck_141_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_node_131_);
lean_dec(v_v_110_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_141_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
size_t v___x_135_; size_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_135_ = lean_usize_shift_right(v_x_95_, v___x_100_);
v___x_136_ = lean_usize_add(v_x_96_, v___x_101_);
v___x_137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_node_131_, v___x_135_, v___x_136_, v_x_97_, v_x_98_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_137_);
v___x_139_ = v___x_133_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
v___y_114_ = v___x_139_;
goto v___jp_113_;
}
}
}
default: 
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v_x_97_);
lean_ctor_set(v___x_142_, 1, v_x_98_);
v___y_114_ = v___x_142_;
goto v___jp_113_;
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_array_fset(v_xs_x27_112_, v_j_104_, v___y_114_);
lean_dec(v_j_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_115_);
v___x_117_ = v___x_108_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
else
{
lean_object* v_ks_145_; lean_object* v_vs_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_166_; 
v_ks_145_ = lean_ctor_get(v_x_94_, 0);
v_vs_146_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_166_ == 0)
{
v___x_148_ = v_x_94_;
v_isShared_149_ = v_isSharedCheck_166_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_vs_146_);
lean_inc(v_ks_145_);
lean_dec(v_x_94_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_166_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_ks_145_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_vs_146_);
v___x_151_ = v_reuseFailAlloc_165_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v_newNode_152_; uint8_t v___y_154_; size_t v___x_160_; uint8_t v___x_161_; 
v_newNode_152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v___x_151_, v_x_97_, v_x_98_);
v___x_160_ = ((size_t)7ULL);
v___x_161_ = lean_usize_dec_le(v___x_160_, v_x_96_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_162_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_152_);
v___x_163_ = lean_unsigned_to_nat(4u);
v___x_164_ = lean_nat_dec_lt(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
v___y_154_ = v___x_164_;
goto v___jp_153_;
}
else
{
v___y_154_ = v___x_161_;
goto v___jp_153_;
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
lean_object* v_ks_155_; lean_object* v_vs_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_ks_155_ = lean_ctor_get(v_newNode_152_, 0);
lean_inc_ref(v_ks_155_);
v_vs_156_ = lean_ctor_get(v_newNode_152_, 1);
lean_inc_ref(v_vs_156_);
lean_dec_ref(v_newNode_152_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_96_, v_ks_155_, v_vs_156_, v___x_157_, v___x_158_);
lean_dec_ref(v_vs_156_);
lean_dec_ref(v_ks_155_);
return v___x_159_;
}
else
{
return v_newNode_152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_167_, lean_object* v_keys_168_, lean_object* v_vals_169_, lean_object* v_i_170_, lean_object* v_entries_171_){
_start:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_array_get_size(v_keys_168_);
v___x_173_ = lean_nat_dec_lt(v_i_170_, v___x_172_);
if (v___x_173_ == 0)
{
lean_dec(v_i_170_);
return v_entries_171_;
}
else
{
lean_object* v_k_174_; lean_object* v_v_175_; uint64_t v___x_176_; size_t v_h_177_; size_t v___x_178_; lean_object* v___x_179_; size_t v___x_180_; size_t v___x_181_; size_t v___x_182_; size_t v_h_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_k_174_ = lean_array_fget_borrowed(v_keys_168_, v_i_170_);
v_v_175_ = lean_array_fget_borrowed(v_vals_169_, v_i_170_);
v___x_176_ = l_Lean_instHashableMVarId_hash(v_k_174_);
v_h_177_ = lean_uint64_to_usize(v___x_176_);
v___x_178_ = ((size_t)5ULL);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_sub(v_depth_167_, v___x_180_);
v___x_182_ = lean_usize_mul(v___x_178_, v___x_181_);
v_h_183_ = lean_usize_shift_right(v_h_177_, v___x_182_);
v___x_184_ = lean_nat_add(v_i_170_, v___x_179_);
lean_dec(v_i_170_);
lean_inc(v_v_175_);
lean_inc(v_k_174_);
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_entries_171_, v_h_183_, v_depth_167_, v_k_174_, v_v_175_);
v_i_170_ = v___x_184_;
v_entries_171_ = v___x_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_187_, lean_object* v_keys_188_, lean_object* v_vals_189_, lean_object* v_i_190_, lean_object* v_entries_191_){
_start:
{
size_t v_depth_boxed_192_; lean_object* v_res_193_; 
v_depth_boxed_192_ = lean_unbox_usize(v_depth_187_);
lean_dec(v_depth_187_);
v_res_193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_192_, v_keys_188_, v_vals_189_, v_i_190_, v_entries_191_);
lean_dec_ref(v_vals_189_);
lean_dec_ref(v_keys_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_4591__boxed_199_; size_t v_x_4592__boxed_200_; lean_object* v_res_201_; 
v_x_4591__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_x_4592__boxed_200_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_res_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_194_, v_x_4591__boxed_199_, v_x_4592__boxed_200_, v_x_197_, v_x_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
uint64_t v___x_205_; size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; 
v___x_205_ = l_Lean_instHashableMVarId_hash(v_x_203_);
v___x_206_ = lean_uint64_to_usize(v___x_205_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_202_, v___x_206_, v___x_207_, v_x_203_, v_x_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(lean_object* v_mvarId_209_, lean_object* v_val_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_mctx_214_; lean_object* v_cache_215_; lean_object* v_zetaDeltaFVarIds_216_; lean_object* v_postponed_217_; lean_object* v_diag_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_245_; 
v___x_213_ = lean_st_ref_take(v___y_211_);
v_mctx_214_ = lean_ctor_get(v___x_213_, 0);
v_cache_215_ = lean_ctor_get(v___x_213_, 1);
v_zetaDeltaFVarIds_216_ = lean_ctor_get(v___x_213_, 2);
v_postponed_217_ = lean_ctor_get(v___x_213_, 3);
v_diag_218_ = lean_ctor_get(v___x_213_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_245_ == 0)
{
v___x_220_ = v___x_213_;
v_isShared_221_ = v_isSharedCheck_245_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_diag_218_);
lean_inc(v_postponed_217_);
lean_inc(v_zetaDeltaFVarIds_216_);
lean_inc(v_cache_215_);
lean_inc(v_mctx_214_);
lean_dec(v___x_213_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_245_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_depth_222_; lean_object* v_levelAssignDepth_223_; lean_object* v_mvarCounter_224_; lean_object* v_lDepth_225_; lean_object* v_decls_226_; lean_object* v_userNames_227_; lean_object* v_lAssignment_228_; lean_object* v_eAssignment_229_; lean_object* v_dAssignment_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_244_; 
v_depth_222_ = lean_ctor_get(v_mctx_214_, 0);
v_levelAssignDepth_223_ = lean_ctor_get(v_mctx_214_, 1);
v_mvarCounter_224_ = lean_ctor_get(v_mctx_214_, 2);
v_lDepth_225_ = lean_ctor_get(v_mctx_214_, 3);
v_decls_226_ = lean_ctor_get(v_mctx_214_, 4);
v_userNames_227_ = lean_ctor_get(v_mctx_214_, 5);
v_lAssignment_228_ = lean_ctor_get(v_mctx_214_, 6);
v_eAssignment_229_ = lean_ctor_get(v_mctx_214_, 7);
v_dAssignment_230_ = lean_ctor_get(v_mctx_214_, 8);
v_isSharedCheck_244_ = !lean_is_exclusive(v_mctx_214_);
if (v_isSharedCheck_244_ == 0)
{
v___x_232_ = v_mctx_214_;
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_dAssignment_230_);
lean_inc(v_eAssignment_229_);
lean_inc(v_lAssignment_228_);
lean_inc(v_userNames_227_);
lean_inc(v_decls_226_);
lean_inc(v_lDepth_225_);
lean_inc(v_mvarCounter_224_);
lean_inc(v_levelAssignDepth_223_);
lean_inc(v_depth_222_);
lean_dec(v_mctx_214_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_244_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_229_, v_mvarId_209_, v_val_210_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 7, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_depth_222_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_levelAssignDepth_223_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_mvarCounter_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_lDepth_225_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_decls_226_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_userNames_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_lAssignment_228_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 8, v_dAssignment_230_);
v___x_236_ = v_reuseFailAlloc_243_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_236_);
v___x_238_ = v___x_220_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_cache_215_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_zetaDeltaFVarIds_216_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_postponed_217_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_diag_218_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_st_ref_set(v___y_211_, v___x_238_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(v_mvarId_246_, v_val_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(lean_object* v_msgData_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_env_258_; lean_object* v___x_259_; lean_object* v_mctx_260_; lean_object* v_lctx_261_; lean_object* v_options_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_257_ = lean_st_ref_get(v___y_255_);
v_env_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_env_258_);
lean_dec(v___x_257_);
v___x_259_ = lean_st_ref_get(v___y_253_);
v_mctx_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_mctx_260_);
lean_dec(v___x_259_);
v_lctx_261_ = lean_ctor_get(v___y_252_, 2);
v_options_262_ = lean_ctor_get(v___y_254_, 2);
lean_inc_ref(v_options_262_);
lean_inc_ref(v_lctx_261_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_258_);
lean_ctor_set(v___x_263_, 1, v_mctx_260_);
lean_ctor_set(v___x_263_, 2, v_lctx_261_);
lean_ctor_set(v___x_263_, 3, v_options_262_);
v___x_264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_msgData_251_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0___boxed(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msgData_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_ref_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_289_; 
v_ref_279_ = lean_ctor_get(v___y_276_, 5);
v___x_280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_289_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_289_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
lean_inc(v_ref_279_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_ref_279_);
lean_ctor_set(v___x_285_, 1, v_a_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set_tag(v___x_283_, 1);
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg___boxed(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
static lean_object* _init_l_elabAsAuxLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_elabAsAuxLemma___lam__0___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0(lean_object* v___x_300_, uint8_t v___x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_303_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___x_311_);
v___x_348_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_348_, 0, v___x_300_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v_a_312_);
v___x_349_ = l_Lean_Elab_Tactic_run(v_a_312_, v___x_348_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; uint8_t v___x_351_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_349_);
v___x_351_ = l_List_isEmpty___redArg(v_a_350_);
lean_dec(v_a_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_a_312_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
v___x_352_ = lean_obj_once(&l_elabAsAuxLemma___lam__0___closed__1, &l_elabAsAuxLemma___lam__0___closed__1_once, _init_l_elabAsAuxLemma___lam__0___closed__1);
v___x_353_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v___x_352_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v___x_353_;
}
else
{
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
v___y_319_ = v___y_307_;
v___y_320_ = v___y_308_;
v___y_321_ = v___y_309_;
goto v___jp_313_;
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_a_312_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
v_a_354_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_349_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_349_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
v___jp_313_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_325_; 
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_inc(v_a_312_);
v___x_322_ = l_Lean_mkMVar(v_a_312_);
v___x_323_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v___x_322_, v___y_319_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v___x_323_);
lean_inc(v_a_312_);
v___x_325_ = l_Lean_MVarId_getType(v_a_312_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_325_);
v___x_327_ = 0;
v___x_328_ = lean_box(0);
lean_inc(v___y_319_);
v___x_329_ = l_Lean_Meta_mkAuxTheorem(v_a_326_, v_a_324_, v___x_327_, v___x_328_, v___x_301_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref(v___x_329_);
v___x_331_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(v_a_312_, v_a_330_, v___y_319_);
lean_dec(v___y_319_);
return v___x_331_;
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v___y_319_);
lean_dec(v_a_312_);
v_a_332_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_329_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_329_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_324_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v_a_312_);
v_a_340_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_325_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_325_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___x_300_);
v_a_362_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_311_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_311_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lam__0___boxed(lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_4878__boxed_381_; lean_object* v_res_382_; 
v___x_4878__boxed_381_ = lean_unbox(v___x_371_);
v_res_382_ = l_elabAsAuxLemma___lam__0(v___x_370_, v___x_4878__boxed_381_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_382_;
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__6(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_elabAsAuxLemma___closed__5));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma(lean_object* v_x_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = ((lean_object*)(l_elabAsAuxLemma___closed__4));
lean_inc(v_x_395_);
v___x_406_ = l_Lean_Syntax_isOfKind(v_x_395_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_x_395_);
v___x_407_ = lean_obj_once(&l_elabAsAuxLemma___closed__6, &l_elabAsAuxLemma___closed__6_once, _init_l_elabAsAuxLemma___closed__6);
v___x_408_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v___x_407_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___f_412_; lean_object* v___x_413_; 
v___x_409_ = lean_unsigned_to_nat(2u);
v___x_410_ = l_Lean_Syntax_getArg(v_x_395_, v___x_409_);
lean_dec(v_x_395_);
v___x_411_ = lean_box(v___x_406_);
v___f_412_ = lean_alloc_closure((void*)(l_elabAsAuxLemma___lam__0___boxed), 11, 2);
lean_closure_set(v___f_412_, 0, v___x_410_);
lean_closure_set(v___f_412_, 1, v___x_411_);
v___x_413_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_412_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___boxed(lean_object* v_x_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_elabAsAuxLemma(v_x_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0(lean_object* v_00_u03b1_425_, lean_object* v_msg_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(v_msg_426_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabAsAuxLemma_spec__0___boxed(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0(v_00_u03b1_437_, v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(lean_object* v_mvarId_449_, lean_object* v_val_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(v_mvarId_449_, v_val_450_, v___y_456_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___boxed(lean_object* v_mvarId_461_, lean_object* v_val_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(v_mvarId_461_, v_val_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_x_474_, v_x_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_478_, lean_object* v_x_479_, size_t v_x_480_, size_t v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_479_, v_x_480_, v_x_481_, v_x_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_485_, lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
size_t v_x_5185__boxed_491_; size_t v_x_5186__boxed_492_; lean_object* v_res_493_; 
v_x_5185__boxed_491_ = lean_unbox_usize(v_x_487_);
lean_dec(v_x_487_);
v_x_5186__boxed_492_ = lean_unbox_usize(v_x_488_);
lean_dec(v_x_488_);
v_res_493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_485_, v_x_486_, v_x_5185__boxed_491_, v_x_5186__boxed_492_, v_x_489_, v_x_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_494_, lean_object* v_n_495_, lean_object* v_k_496_, lean_object* v_v_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_495_, v_k_496_, v_v_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_499_, size_t v_depth_500_, lean_object* v_keys_501_, lean_object* v_vals_502_, lean_object* v_heq_503_, lean_object* v_i_504_, lean_object* v_entries_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_500_, v_keys_501_, v_vals_502_, v_i_504_, v_entries_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_507_, lean_object* v_depth_508_, lean_object* v_keys_509_, lean_object* v_vals_510_, lean_object* v_heq_511_, lean_object* v_i_512_, lean_object* v_entries_513_){
_start:
{
size_t v_depth_boxed_514_; lean_object* v_res_515_; 
v_depth_boxed_514_ = lean_unbox_usize(v_depth_508_);
lean_dec(v_depth_508_);
v_res_515_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_507_, v_depth_boxed_514_, v_keys_509_, v_vals_510_, v_heq_511_, v_i_512_, v_entries_513_);
lean_dec_ref(v_vals_510_);
lean_dec_ref(v_keys_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_517_, v_x_518_, v_x_519_, v_x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1(){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_527_ = ((lean_object*)(l_elabAsAuxLemma___closed__4));
v___x_528_ = ((lean_object*)(l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1));
v___x_529_ = lean_alloc_closure((void*)(l_elabAsAuxLemma___boxed), 10, 0);
v___x_530_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_526_, v___x_527_, v___x_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___boxed(lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
return v_res_532_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
}
#ifdef __cplusplus
}
#endif
