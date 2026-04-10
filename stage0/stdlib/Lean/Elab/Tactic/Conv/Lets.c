// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Lets
// Imports: public import Lean.Elab.Tactic.Lets public import Lean.Elab.Tactic.Conv.Basic
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "(internal error) non-defeq in assignment"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "made no progress"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(lean_object*, lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extract_lets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 33, 143, 120, 246, 234, 114, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value),LEAN_SCALAR_PTR_LITERAL(84, 111, 123, 142, 92, 98, 88, 43)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalExtractLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 244, 234, 55, 146, 240, 50, 65)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lift_lets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 227, 82, 255, 128, 171, 101)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 68, 102, 93, 72, 158, 25, 211)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalLiftLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 101, 191, 197, 167, 255, 65, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let_to_have"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 121, 21, 93, 142, 174, 18, 85)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 168, 69, 201, 229, 158, 224, 21)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalLetToHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 117, 55, 170, 83, 87, 254, 102)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(lean_object* v_mvarId_31_, lean_object* v_x_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_31_, v_x_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
else
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
v_a_47_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___x_38_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_38_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(lean_object* v_mvarId_55_, lean_object* v_x_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_55_, v_x_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(lean_object* v_00_u03b1_63_, lean_object* v_mvarId_64_, lean_object* v_x_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvarId_64_, v_x_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(lean_object* v_00_u03b1_72_, lean_object* v_mvarId_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(v_00_u03b1_72_, v_mvarId_73_, v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(lean_object* v_k_81_, lean_object* v_b_82_, lean_object* v_c_83_, lean_object* v_d_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
v___x_90_ = lean_apply_8(v_k_81_, v_b_82_, v_c_83_, v_d_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, lean_box(0));
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(lean_object* v_k_91_, lean_object* v_b_92_, lean_object* v_c_93_, lean_object* v_d_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_91_, v_b_92_, v_c_93_, v_d_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(lean_object* v_es_101_, lean_object* v_givenNames_102_, lean_object* v_k_103_, lean_object* v_config_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_110_, 0, v_k_103_);
v___x_111_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(lean_box(0), v_es_101_, v_givenNames_102_, v___f_110_, v_config_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_111_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_111_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(lean_object* v_es_128_, lean_object* v_givenNames_129_, lean_object* v_k_130_, lean_object* v_config_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_128_, v_givenNames_129_, v_k_130_, v_config_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec_ref(v_config_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(lean_object* v_00_u03b1_138_, lean_object* v_es_139_, lean_object* v_givenNames_140_, lean_object* v_k_141_, lean_object* v_config_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v_es_139_, v_givenNames_140_, v_k_141_, v_config_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(lean_object* v_00_u03b1_149_, lean_object* v_es_150_, lean_object* v_givenNames_151_, lean_object* v_k_152_, lean_object* v_config_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(v_00_u03b1_149_, v_es_150_, v_givenNames_151_, v_k_152_, v_config_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec_ref(v_config_153_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_ks_164_; lean_object* v_vs_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_189_; 
v_ks_164_ = lean_ctor_get(v_x_160_, 0);
v_vs_165_ = lean_ctor_get(v_x_160_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_189_ == 0)
{
v___x_167_ = v_x_160_;
v_isShared_168_ = v_isSharedCheck_189_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_vs_165_);
lean_inc(v_ks_164_);
lean_dec(v_x_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_189_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_array_get_size(v_ks_164_);
v___x_170_ = lean_nat_dec_lt(v_x_161_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec(v_x_161_);
v___x_171_ = lean_array_push(v_ks_164_, v_x_162_);
v___x_172_ = lean_array_push(v_vs_165_, v_x_163_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_172_);
lean_ctor_set(v___x_167_, 0, v___x_171_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v_k_x27_176_; uint8_t v___x_177_; 
v_k_x27_176_ = lean_array_fget_borrowed(v_ks_164_, v_x_161_);
v___x_177_ = l_Lean_instBEqMVarId_beq(v_x_162_, v_k_x27_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_179_; 
if (v_isShared_168_ == 0)
{
v___x_179_ = v___x_167_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_ks_164_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_vs_165_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_x_161_, v___x_180_);
lean_dec(v_x_161_);
v_x_160_ = v___x_179_;
v_x_161_ = v___x_181_;
goto _start;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_array_fset(v_ks_164_, v_x_161_, v_x_162_);
v___x_185_ = lean_array_fset(v_vs_165_, v_x_161_, v_x_163_);
lean_dec(v_x_161_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_185_);
lean_ctor_set(v___x_167_, 0, v___x_184_);
v___x_187_ = v___x_167_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(lean_object* v_n_190_, lean_object* v_k_191_, lean_object* v_v_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_n_190_, v___x_193_, v_k_191_, v_v_192_);
return v___x_194_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; 
v___x_195_ = ((size_t)5ULL);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_shift_left(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; 
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0);
v___x_200_ = lean_usize_sub(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(lean_object* v_x_202_, size_t v_x_203_, size_t v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v_es_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; lean_object* v_j_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_es_207_ = lean_ctor_get(v_x_202_, 0);
v___x_208_ = ((size_t)5ULL);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1);
v___x_211_ = lean_usize_land(v_x_203_, v___x_210_);
v_j_212_ = lean_usize_to_nat(v___x_211_);
v___x_213_ = lean_array_get_size(v_es_207_);
v___x_214_ = lean_nat_dec_lt(v_j_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_j_212_);
lean_dec(v_x_206_);
lean_dec(v_x_205_);
return v_x_202_;
}
else
{
lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_251_; 
lean_inc_ref(v_es_207_);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_x_202_, 0);
lean_dec(v_unused_252_);
v___x_216_ = v_x_202_;
v_isShared_217_ = v_isSharedCheck_251_;
goto v_resetjp_215_;
}
else
{
lean_dec(v_x_202_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_251_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_v_218_; lean_object* v___x_219_; lean_object* v_xs_x27_220_; lean_object* v___y_222_; 
v_v_218_ = lean_array_fget(v_es_207_, v_j_212_);
v___x_219_ = lean_box(0);
v_xs_x27_220_ = lean_array_fset(v_es_207_, v_j_212_, v___x_219_);
switch(lean_obj_tag(v_v_218_))
{
case 0:
{
lean_object* v_key_227_; lean_object* v_val_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_238_; 
v_key_227_ = lean_ctor_get(v_v_218_, 0);
v_val_228_ = lean_ctor_get(v_v_218_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v_v_218_);
if (v_isSharedCheck_238_ == 0)
{
v___x_230_ = v_v_218_;
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_val_228_);
lean_inc(v_key_227_);
lean_dec(v_v_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_238_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; 
v___x_232_ = l_Lean_instBEqMVarId_beq(v_x_205_, v_key_227_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_230_);
v___x_233_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_227_, v_val_228_, v_x_205_, v_x_206_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
else
{
lean_object* v___x_236_; 
lean_dec(v_val_228_);
lean_dec(v_key_227_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_x_206_);
lean_ctor_set(v___x_230_, 0, v_x_205_);
v___x_236_ = v___x_230_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_x_205_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_x_206_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v___y_222_ = v___x_236_;
goto v___jp_221_;
}
}
}
}
case 1:
{
lean_object* v_node_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_249_; 
v_node_239_ = lean_ctor_get(v_v_218_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_v_218_);
if (v_isSharedCheck_249_ == 0)
{
v___x_241_ = v_v_218_;
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_node_239_);
lean_dec(v_v_218_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_249_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_243_ = lean_usize_shift_right(v_x_203_, v___x_208_);
v___x_244_ = lean_usize_add(v_x_204_, v___x_209_);
v___x_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_node_239_, v___x_243_, v___x_244_, v_x_205_, v_x_206_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_245_);
v___x_247_ = v___x_241_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v___y_222_ = v___x_247_;
goto v___jp_221_;
}
}
}
default: 
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_x_205_);
lean_ctor_set(v___x_250_, 1, v_x_206_);
v___y_222_ = v___x_250_;
goto v___jp_221_;
}
}
v___jp_221_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_array_fset(v_xs_x27_220_, v_j_212_, v___y_222_);
lean_dec(v_j_212_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_223_);
v___x_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
else
{
lean_object* v_ks_253_; lean_object* v_vs_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_274_; 
v_ks_253_ = lean_ctor_get(v_x_202_, 0);
v_vs_254_ = lean_ctor_get(v_x_202_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_274_ == 0)
{
v___x_256_ = v_x_202_;
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_vs_254_);
lean_inc(v_ks_253_);
lean_dec(v_x_202_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_ks_253_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_vs_254_);
v___x_259_ = v_reuseFailAlloc_273_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v_newNode_260_; uint8_t v___y_262_; size_t v___x_268_; uint8_t v___x_269_; 
v_newNode_260_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v___x_259_, v_x_205_, v_x_206_);
v___x_268_ = ((size_t)7ULL);
v___x_269_ = lean_usize_dec_le(v___x_268_, v_x_204_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_260_);
v___x_271_ = lean_unsigned_to_nat(4u);
v___x_272_ = lean_nat_dec_lt(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
v___y_262_ = v___x_272_;
goto v___jp_261_;
}
else
{
v___y_262_ = v___x_269_;
goto v___jp_261_;
}
v___jp_261_:
{
if (v___y_262_ == 0)
{
lean_object* v_ks_263_; lean_object* v_vs_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_ks_263_ = lean_ctor_get(v_newNode_260_, 0);
lean_inc_ref(v_ks_263_);
v_vs_264_ = lean_ctor_get(v_newNode_260_, 1);
lean_inc_ref(v_vs_264_);
lean_dec_ref(v_newNode_260_);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2);
v___x_267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_x_204_, v_ks_263_, v_vs_264_, v___x_265_, v___x_266_);
lean_dec_ref(v_vs_264_);
lean_dec_ref(v_ks_263_);
return v___x_267_;
}
else
{
return v_newNode_260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(size_t v_depth_275_, lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_entries_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_array_get_size(v_keys_276_);
v___x_281_ = lean_nat_dec_lt(v_i_278_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec(v_i_278_);
return v_entries_279_;
}
else
{
lean_object* v_k_282_; lean_object* v_v_283_; uint64_t v___x_284_; size_t v_h_285_; size_t v___x_286_; lean_object* v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v_h_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_k_282_ = lean_array_fget_borrowed(v_keys_276_, v_i_278_);
v_v_283_ = lean_array_fget_borrowed(v_vals_277_, v_i_278_);
v___x_284_ = l_Lean_instHashableMVarId_hash(v_k_282_);
v_h_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = ((size_t)5ULL);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_sub(v_depth_275_, v___x_288_);
v___x_290_ = lean_usize_mul(v___x_286_, v___x_289_);
v_h_291_ = lean_usize_shift_right(v_h_285_, v___x_290_);
v___x_292_ = lean_nat_add(v_i_278_, v___x_287_);
lean_dec(v_i_278_);
lean_inc(v_v_283_);
lean_inc(v_k_282_);
v___x_293_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_entries_279_, v_h_291_, v_depth_275_, v_k_282_, v_v_283_);
v_i_278_ = v___x_292_;
v_entries_279_ = v___x_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_depth_295_, lean_object* v_keys_296_, lean_object* v_vals_297_, lean_object* v_i_298_, lean_object* v_entries_299_){
_start:
{
size_t v_depth_boxed_300_; lean_object* v_res_301_; 
v_depth_boxed_300_ = lean_unbox_usize(v_depth_295_);
lean_dec(v_depth_295_);
v_res_301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_boxed_300_, v_keys_296_, v_vals_297_, v_i_298_, v_entries_299_);
lean_dec_ref(v_vals_297_);
lean_dec_ref(v_keys_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
size_t v_x_6143__boxed_307_; size_t v_x_6144__boxed_308_; lean_object* v_res_309_; 
v_x_6143__boxed_307_ = lean_unbox_usize(v_x_303_);
lean_dec(v_x_303_);
v_x_6144__boxed_308_ = lean_unbox_usize(v_x_304_);
lean_dec(v_x_304_);
v_res_309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_302_, v_x_6143__boxed_307_, v_x_6144__boxed_308_, v_x_305_, v_x_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint64_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_313_ = l_Lean_instHashableMVarId_hash(v_x_311_);
v___x_314_ = lean_uint64_to_usize(v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_310_, v___x_314_, v___x_315_, v_x_311_, v_x_312_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(lean_object* v_mvarId_317_, lean_object* v_val_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v_mctx_322_; lean_object* v_cache_323_; lean_object* v_zetaDeltaFVarIds_324_; lean_object* v_postponed_325_; lean_object* v_diag_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_354_; 
v___x_321_ = lean_st_ref_take(v___y_319_);
v_mctx_322_ = lean_ctor_get(v___x_321_, 0);
v_cache_323_ = lean_ctor_get(v___x_321_, 1);
v_zetaDeltaFVarIds_324_ = lean_ctor_get(v___x_321_, 2);
v_postponed_325_ = lean_ctor_get(v___x_321_, 3);
v_diag_326_ = lean_ctor_get(v___x_321_, 4);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_354_ == 0)
{
v___x_328_ = v___x_321_;
v_isShared_329_ = v_isSharedCheck_354_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_diag_326_);
lean_inc(v_postponed_325_);
lean_inc(v_zetaDeltaFVarIds_324_);
lean_inc(v_cache_323_);
lean_inc(v_mctx_322_);
lean_dec(v___x_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_354_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_depth_330_; lean_object* v_levelAssignDepth_331_; lean_object* v_lmvarCounter_332_; lean_object* v_mvarCounter_333_; lean_object* v_lDecls_334_; lean_object* v_decls_335_; lean_object* v_userNames_336_; lean_object* v_lAssignment_337_; lean_object* v_eAssignment_338_; lean_object* v_dAssignment_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_353_; 
v_depth_330_ = lean_ctor_get(v_mctx_322_, 0);
v_levelAssignDepth_331_ = lean_ctor_get(v_mctx_322_, 1);
v_lmvarCounter_332_ = lean_ctor_get(v_mctx_322_, 2);
v_mvarCounter_333_ = lean_ctor_get(v_mctx_322_, 3);
v_lDecls_334_ = lean_ctor_get(v_mctx_322_, 4);
v_decls_335_ = lean_ctor_get(v_mctx_322_, 5);
v_userNames_336_ = lean_ctor_get(v_mctx_322_, 6);
v_lAssignment_337_ = lean_ctor_get(v_mctx_322_, 7);
v_eAssignment_338_ = lean_ctor_get(v_mctx_322_, 8);
v_dAssignment_339_ = lean_ctor_get(v_mctx_322_, 9);
v_isSharedCheck_353_ = !lean_is_exclusive(v_mctx_322_);
if (v_isSharedCheck_353_ == 0)
{
v___x_341_ = v_mctx_322_;
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_dAssignment_339_);
lean_inc(v_eAssignment_338_);
lean_inc(v_lAssignment_337_);
lean_inc(v_userNames_336_);
lean_inc(v_decls_335_);
lean_inc(v_lDecls_334_);
lean_inc(v_mvarCounter_333_);
lean_inc(v_lmvarCounter_332_);
lean_inc(v_levelAssignDepth_331_);
lean_inc(v_depth_330_);
lean_dec(v_mctx_322_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_eAssignment_338_, v_mvarId_317_, v_val_318_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 8, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_depth_330_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_levelAssignDepth_331_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_lmvarCounter_332_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_mvarCounter_333_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_lDecls_334_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v_decls_335_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_userNames_336_);
lean_ctor_set(v_reuseFailAlloc_352_, 7, v_lAssignment_337_);
lean_ctor_set(v_reuseFailAlloc_352_, 8, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_352_, 9, v_dAssignment_339_);
v___x_345_ = v_reuseFailAlloc_352_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_345_);
v___x_347_ = v___x_328_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_cache_323_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_zetaDeltaFVarIds_324_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_postponed_325_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_diag_326_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_st_ref_set(v___y_319_, v___x_347_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(lean_object* v_mvarId_355_, lean_object* v_val_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_355_, v_val_356_, v___y_357_);
lean_dec(v___y_357_);
return v_res_359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(lean_object* v___x_365_, lean_object* v_a_366_, lean_object* v___x_367_, lean_object* v_a_368_, lean_object* v_mvar_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
lean_inc_ref(v_a_366_);
v___x_375_ = l_Lean_Meta_isExprDefEq(v___x_365_, v_a_366_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; uint8_t v___x_377_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
v___x_377_ = lean_unbox(v_a_376_);
lean_dec(v_a_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2);
v___x_379_ = l_Lean_Meta_throwTacticEx___redArg(v___x_367_, v_a_368_, v___x_378_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; 
lean_dec_ref(v___x_379_);
v___x_380_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_369_, v_a_366_, v___y_371_);
return v___x_380_;
}
else
{
lean_dec(v_mvar_369_);
lean_dec_ref(v_a_366_);
return v___x_379_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v_a_368_);
lean_dec(v___x_367_);
v___x_381_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_369_, v_a_366_, v___y_371_);
return v___x_381_;
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_mvar_369_);
lean_dec(v_a_368_);
lean_dec(v___x_367_);
lean_dec_ref(v_a_366_);
v_a_382_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_375_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_375_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(lean_object* v___x_390_, lean_object* v_a_391_, lean_object* v___x_392_, lean_object* v_a_393_, lean_object* v_mvar_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(v___x_390_, v_a_391_, v___x_392_, v_a_393_, v_mvar_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(lean_object* v___x_401_, uint8_t v___x_402_, lean_object* v___x_403_, lean_object* v_a_404_, lean_object* v_mvar_405_, lean_object* v_e_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_412_ = 0;
v___x_413_ = 1;
v___x_414_ = l_Lean_Meta_mkLetFVars(v___x_401_, v_e_406_, v___x_412_, v___x_402_, v___x_413_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
lean_inc_n(v_mvar_405_, 2);
v___x_416_ = l_Lean_Expr_mvar___override(v_mvar_405_);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed), 10, 5);
lean_closure_set(v___f_417_, 0, v___x_416_);
lean_closure_set(v___f_417_, 1, v_a_415_);
lean_closure_set(v___f_417_, 2, v___x_403_);
lean_closure_set(v___f_417_, 3, v_a_404_);
lean_closure_set(v___f_417_, 4, v_mvar_405_);
v___x_418_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvar_405_, v___f_417_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_418_;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_mvar_405_);
lean_dec(v_a_404_);
lean_dec(v___x_403_);
v_a_419_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_414_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_414_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_a_430_, lean_object* v_mvar_431_, lean_object* v_e_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___x_6437__boxed_438_; lean_object* v_res_439_; 
v___x_6437__boxed_438_ = lean_unbox(v___x_428_);
v_res_439_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_427_, v___x_6437__boxed_438_, v___x_429_, v_a_430_, v_mvar_431_, v_e_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec_ref(v___x_427_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_443_ == 0)
{
return v_bs_442_;
}
else
{
lean_object* v_v_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_444_ = lean_array_uget(v_bs_442_, v_i_441_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_445_);
v___x_447_ = l_Lean_Expr_fvar___override(v_v_444_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_446_, v_i_441_, v___x_447_);
v_i_441_ = v___x_449_;
v_bs_442_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(lean_object* v___x_463_, lean_object* v_a_464_, size_t v___x_465_, uint8_t v___x_466_, lean_object* v___x_467_, lean_object* v_snd_468_, lean_object* v_fst_469_, lean_object* v_fvarIds_470_, lean_object* v_es_471_, lean_object* v_x_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___y_543_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_478_ = l_Lean_instInhabitedExpr;
v___x_479_ = lean_array_get_borrowed(v___x_478_, v_es_471_, v___x_463_);
v___x_554_ = lean_array_get_size(v_fvarIds_470_);
v___x_555_ = lean_nat_dec_eq(v___x_554_, v___x_463_);
if (v___x_555_ == 0)
{
v___y_543_ = v___x_555_;
goto v___jp_542_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = lean_expr_eqv(v_fst_469_, v___x_479_);
v___y_543_ = v___x_556_;
goto v___jp_542_;
}
v___jp_480_:
{
lean_object* v___x_481_; 
lean_inc(v_a_464_);
v___x_481_ = l_Lean_MVarId_getTag(v_a_464_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_481_);
lean_inc(v___x_479_);
v___x_483_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_479_, v_a_482_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_525_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
v_fst_485_ = lean_ctor_get(v_a_484_, 0);
v_snd_486_ = lean_ctor_get(v_a_484_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_a_484_);
if (v_isSharedCheck_525_ == 0)
{
v___x_488_ = v_a_484_;
v_isShared_489_ = v_isSharedCheck_525_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_486_);
lean_inc(v_fst_485_);
lean_dec(v_a_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_525_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
size_t v_sz_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_sz_490_ = lean_array_size(v_fvarIds_470_);
lean_inc_ref(v_fvarIds_470_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_490_, v___x_465_, v_fvarIds_470_);
v___x_492_ = l_Lean_Expr_mvarId_x21(v_fst_485_);
lean_dec(v_fst_485_);
lean_inc(v_a_464_);
lean_inc(v___x_467_);
v___x_493_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_491_, v___x_466_, v___x_467_, v_a_464_, v___x_492_, v_snd_468_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v___x_493_);
lean_inc(v_snd_486_);
lean_inc(v_a_464_);
v___x_494_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(v___x_491_, v___x_466_, v___x_467_, v_a_464_, v_a_464_, v_snd_486_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec_ref(v___x_491_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_494_, 0);
lean_dec(v_unused_508_);
v___x_496_ = v___x_494_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_dec(v___x_494_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_498_ = l_Lean_Expr_mvarId_x21(v_snd_486_);
lean_dec(v_snd_486_);
v___x_499_ = lean_box(0);
v___x_500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_500_);
lean_ctor_set(v___x_488_, 0, v_fvarIds_470_);
v___x_502_ = v___x_488_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_fvarIds_470_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_506_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_502_);
v___x_504_ = v___x_496_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_del_object(v___x_488_);
lean_dec(v_snd_486_);
lean_dec_ref(v_fvarIds_470_);
v_a_509_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_494_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_494_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v___x_491_);
lean_del_object(v___x_488_);
lean_dec(v_snd_486_);
lean_dec_ref(v_fvarIds_470_);
lean_dec(v___x_467_);
lean_dec(v_a_464_);
v_a_517_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_493_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_493_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_fvarIds_470_);
lean_dec_ref(v_snd_468_);
lean_dec(v___x_467_);
lean_dec(v_a_464_);
v_a_526_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_483_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_483_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_fvarIds_470_);
lean_dec_ref(v_snd_468_);
lean_dec(v___x_467_);
lean_dec(v_a_464_);
v_a_534_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_481_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_481_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
v___jp_542_:
{
if (v___y_543_ == 0)
{
goto v___jp_480_;
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
lean_inc(v_a_464_);
lean_inc(v___x_467_);
v___x_545_ = l_Lean_Meta_throwTacticEx___redArg(v___x_467_, v_a_464_, v___x_544_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_dec_ref(v___x_545_);
goto v___jp_480_;
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v_fvarIds_470_);
lean_dec_ref(v_snd_468_);
lean_dec(v___x_467_);
lean_dec(v_a_464_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(lean_object* v___x_557_, lean_object* v_a_558_, lean_object* v___x_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v_snd_562_, lean_object* v_fst_563_, lean_object* v_fvarIds_564_, lean_object* v_es_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
size_t v___x_6519__boxed_572_; uint8_t v___x_6520__boxed_573_; lean_object* v_res_574_; 
v___x_6519__boxed_572_ = lean_unbox_usize(v___x_559_);
lean_dec(v___x_559_);
v___x_6520__boxed_573_ = lean_unbox(v___x_560_);
v_res_574_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(v___x_557_, v_a_558_, v___x_6519__boxed_572_, v___x_6520__boxed_573_, v___x_561_, v_snd_562_, v_fst_563_, v_fvarIds_564_, v_es_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v_x_566_);
lean_dec_ref(v_es_565_);
lean_dec_ref(v_fst_563_);
lean_dec(v___x_557_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(lean_object* v___x_578_, size_t v___x_579_, uint8_t v___x_580_, lean_object* v_snd_581_, lean_object* v_fst_582_, lean_object* v___x_583_, lean_object* v___x_584_, lean_object* v_a_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_587_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc_n(v_a_596_, 2);
lean_dec_ref(v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1));
v___x_598_ = l_Lean_MVarId_checkNotAssigned(v_a_596_, v___x_597_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec_ref(v___x_598_);
v___x_599_ = lean_box_usize(v___x_579_);
v___x_600_ = lean_box(v___x_580_);
lean_inc_ref(v_fst_582_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed), 15, 7);
lean_closure_set(v___f_601_, 0, v___x_578_);
lean_closure_set(v___f_601_, 1, v_a_596_);
lean_closure_set(v___f_601_, 2, v___x_599_);
lean_closure_set(v___f_601_, 3, v___x_600_);
lean_closure_set(v___f_601_, 4, v___x_597_);
lean_closure_set(v___f_601_, 5, v_snd_581_);
lean_closure_set(v___f_601_, 6, v_fst_582_);
v___x_602_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_603_ = lean_array_push(v___x_602_, v_fst_582_);
v___x_604_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v___x_603_, v___x_584_, v___f_601_, v_a_585_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref(v___x_604_);
v_fst_606_ = lean_ctor_get(v_a_605_, 0);
lean_inc(v_fst_606_);
v_snd_607_ = lean_ctor_get(v_a_605_, 1);
lean_inc(v_snd_607_);
lean_dec(v_a_605_);
v___x_608_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_snd_607_, v___y_587_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_608_, 0);
lean_dec(v_unused_616_);
v___x_610_ = v___x_608_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_dec(v___x_608_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_fst_606_);
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_606_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_fst_606_);
v_a_617_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_608_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_625_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_604_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_604_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_a_596_);
lean_dec(v___x_584_);
lean_dec_ref(v_fst_582_);
lean_dec_ref(v_snd_581_);
lean_dec(v___x_578_);
v_a_633_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_598_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_598_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_584_);
lean_dec_ref(v_fst_582_);
lean_dec_ref(v_snd_581_);
lean_dec(v___x_578_);
v_a_641_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_595_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_595_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(lean_object** _args){
lean_object* v___x_649_ = _args[0];
lean_object* v___x_650_ = _args[1];
lean_object* v___x_651_ = _args[2];
lean_object* v_snd_652_ = _args[3];
lean_object* v_fst_653_ = _args[4];
lean_object* v___x_654_ = _args[5];
lean_object* v___x_655_ = _args[6];
lean_object* v_a_656_ = _args[7];
lean_object* v___y_657_ = _args[8];
lean_object* v___y_658_ = _args[9];
lean_object* v___y_659_ = _args[10];
lean_object* v___y_660_ = _args[11];
lean_object* v___y_661_ = _args[12];
lean_object* v___y_662_ = _args[13];
lean_object* v___y_663_ = _args[14];
lean_object* v___y_664_ = _args[15];
lean_object* v___y_665_ = _args[16];
_start:
{
size_t v___x_6727__boxed_666_; uint8_t v___x_6728__boxed_667_; lean_object* v_res_668_; 
v___x_6727__boxed_666_ = lean_unbox_usize(v___x_650_);
lean_dec(v___x_650_);
v___x_6728__boxed_667_ = lean_unbox(v___x_651_);
v_res_668_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(v___x_649_, v___x_6727__boxed_666_, v___x_6728__boxed_667_, v_snd_652_, v_fst_653_, v___x_654_, v___x_655_, v_a_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v_a_656_);
lean_dec(v___x_654_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(size_t v_sz_669_, size_t v_i_670_, lean_object* v_bs_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = lean_usize_dec_lt(v_i_670_, v_sz_669_);
if (v___x_672_ == 0)
{
return v_bs_671_;
}
else
{
lean_object* v_v_673_; lean_object* v___x_674_; lean_object* v_bs_x27_675_; lean_object* v___x_676_; size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v_v_673_ = lean_array_uget(v_bs_671_, v_i_670_);
v___x_674_ = lean_unsigned_to_nat(0u);
v_bs_x27_675_ = lean_array_uset(v_bs_671_, v_i_670_, v___x_674_);
v___x_676_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_673_);
lean_dec(v_v_673_);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_670_, v___x_677_);
v___x_679_ = lean_array_uset(v_bs_x27_675_, v_i_670_, v___x_676_);
v_i_670_ = v___x_678_;
v_bs_671_ = v___x_679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_bs_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_685_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_boxed_684_, v_i_boxed_685_, v_bs_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5));
lean_inc(v_x_706_);
v___x_717_ = l_Lean_Syntax_isOfKind(v_x_706_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v_x_706_);
v___x_718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = l_Lean_Syntax_getArg(v_x_706_, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7));
lean_inc(v___x_720_);
v___x_722_ = l_Lean_Syntax_isOfKind(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v___x_720_);
lean_dec(v_x_706_);
v___x_723_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_723_;
}
else
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_720_, v_a_707_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref(v___x_724_);
v___x_726_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(v_a_708_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_ids_732_; size_t v_sz_733_; lean_object* v___x_734_; size_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___f_740_; lean_object* v___x_741_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_726_);
v_fst_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_fst_728_);
v_snd_729_ = lean_ctor_get(v_a_727_, 1);
lean_inc(v_snd_729_);
lean_dec(v_a_727_);
v___x_730_ = lean_unsigned_to_nat(2u);
v___x_731_ = l_Lean_Syntax_getArg(v_x_706_, v___x_730_);
lean_dec(v_x_706_);
v_ids_732_ = l_Lean_Syntax_getArgs(v___x_731_);
lean_dec(v___x_731_);
v_sz_733_ = lean_array_size(v_ids_732_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = ((size_t)0ULL);
lean_inc_ref(v_ids_732_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_733_, v___x_735_, v_ids_732_);
v___x_737_ = lean_array_to_list(v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1));
v___x_739_ = lean_box(v___x_722_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed), 17, 8);
lean_closure_set(v___f_740_, 0, v___x_734_);
lean_closure_set(v___f_740_, 1, v___x_738_);
lean_closure_set(v___f_740_, 2, v___x_739_);
lean_closure_set(v___f_740_, 3, v_snd_729_);
lean_closure_set(v___f_740_, 4, v_fst_728_);
lean_closure_set(v___f_740_, 5, v___x_719_);
lean_closure_set(v___f_740_, 6, v___x_737_);
lean_closure_set(v___f_740_, 7, v_a_725_);
v___x_741_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_740_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref(v___x_741_);
v___x_743_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_732_, v_a_742_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
return v___x_743_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_ids_732_);
v_a_744_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_741_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_725_);
lean_dec(v_x_706_);
v_a_752_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_726_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_726_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_x_706_);
v_a_760_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_724_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_724_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(lean_object* v_x_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(v_x_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(lean_object* v_mvarId_779_, lean_object* v_val_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvarId_779_, v_val_780_, v___y_782_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(lean_object* v_mvarId_787_, lean_object* v_val_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(v_mvarId_787_, v_val_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, size_t v_x_802_, size_t v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_801_, v_x_802_, v_x_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
size_t v_x_7091__boxed_813_; size_t v_x_7092__boxed_814_; lean_object* v_res_815_; 
v_x_7091__boxed_813_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_x_7092__boxed_814_ = lean_unbox_usize(v_x_810_);
lean_dec(v_x_810_);
v_res_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(v_00_u03b2_807_, v_x_808_, v_x_7091__boxed_813_, v_x_7092__boxed_814_, v_x_811_, v_x_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_816_, lean_object* v_n_817_, lean_object* v_k_818_, lean_object* v_v_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v_n_817_, v_k_818_, v_v_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_821_, size_t v_depth_822_, lean_object* v_keys_823_, lean_object* v_vals_824_, lean_object* v_heq_825_, lean_object* v_i_826_, lean_object* v_entries_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_822_, v_keys_823_, v_vals_824_, v_i_826_, v_entries_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b2_829_, lean_object* v_depth_830_, lean_object* v_keys_831_, lean_object* v_vals_832_, lean_object* v_heq_833_, lean_object* v_i_834_, lean_object* v_entries_835_){
_start:
{
size_t v_depth_boxed_836_; lean_object* v_res_837_; 
v_depth_boxed_836_ = lean_unbox_usize(v_depth_830_);
lean_dec(v_depth_830_);
v_res_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(v_00_u03b2_829_, v_depth_boxed_836_, v_keys_831_, v_vals_832_, v_heq_833_, v_i_834_, v_entries_835_);
lean_dec_ref(v_vals_832_);
lean_dec_ref(v_keys_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_x_839_, v_x_840_, v_x_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1(){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_854_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5));
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2));
v___x_856_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed), 10, 0);
v___x_857_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_853_, v___x_854_, v___x_855_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(lean_object* v_a_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_865_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc_n(v_a_874_, 2);
lean_dec_ref(v___x_873_);
v___x_875_ = l_Lean_Meta_liftLets(v_a_874_, v_a_863_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; uint8_t v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = lean_expr_eqv(v_a_874_, v_a_876_);
lean_dec(v_a_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_876_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_865_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1));
v___x_882_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
v___x_883_ = l_Lean_Meta_throwTacticEx___redArg(v___x_881_, v_a_880_, v___x_882_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v___x_883_);
v___x_884_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_876_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_884_;
}
else
{
lean_dec(v_a_876_);
return v___x_883_;
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_876_);
v_a_885_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_879_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_879_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_a_874_);
v_a_893_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_875_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_875_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_a_863_);
v_a_901_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_873_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_873_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(lean_object* v_a_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(v_a_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets(lean_object* v_x_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1));
lean_inc(v_x_927_);
v___x_938_ = l_Lean_Syntax_isOfKind(v_x_927_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec(v_x_927_);
v___x_939_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = l_Lean_Syntax_getArg(v_x_927_, v___x_940_);
lean_dec(v_x_927_);
v___x_942_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7));
lean_inc(v___x_941_);
v___x_943_ = l_Lean_Syntax_isOfKind(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_dec(v___x_941_);
v___x_944_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_941_, v_a_928_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___f_947_; lean_object* v___x_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed), 10, 1);
lean_closure_set(v___f_947_, 0, v_a_946_);
v___x_948_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_947_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_948_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_945_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(lean_object* v_x_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(v_x_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1(){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_976_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_977_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1));
v___x_978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1));
v___x_979_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed), 10, 0);
v___x_980_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_976_, v___x_977_, v___x_978_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_987_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_n(v_a_996_, 2);
lean_dec_ref(v___x_995_);
v___x_997_ = l_Lean_Meta_letToHave(v_a_996_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; uint8_t v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = lean_expr_eqv(v_a_996_, v_a_998_);
lean_dec(v_a_996_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_998_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_987_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1));
v___x_1004_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2, &l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
v___x_1005_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1003_, v_a_1002_, v___x_1004_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1006_; 
lean_dec_ref(v___x_1005_);
v___x_1006_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_998_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1006_;
}
else
{
lean_dec(v_a_998_);
return v___x_1005_;
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_998_);
v_a_1007_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1001_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1001_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_a_996_);
v_a_1015_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_997_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_997_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_995_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_995_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave(lean_object* v_x_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1));
v___x_1060_ = l_Lean_Syntax_isOfKind(v_x_1049_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
return v___x_1061_;
}
else
{
lean_object* v___f_1062_; lean_object* v___x_1063_; 
v___f_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2));
v___x_1063_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1062_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(lean_object* v_x_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(v_x_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1(){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1083_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1));
v___x_1085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1));
v___x_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed), 10, 0);
v___x_1087_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1083_, v___x_1084_, v___x_1085_, v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
return v_res_1089_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Lets(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Lets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
}
#ifdef __cplusplus
}
#endif
