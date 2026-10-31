// Lean compiler output
// Module: Lean.Elab.Tactic.Simproc
// Imports: public import Init.Simproc public import Lean.Meta.Tactic.Simp.Simproc public import Lean.Elab.Command
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_elabSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_elabSimprocPattern___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Elab_elabSimprocPattern___closed__0_value;
static const lean_array_object l_Lean_Elab_elabSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_elabSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Elab_elabSimprocPattern___closed__1_value;
static const lean_ctor_object l_Lean_Elab_elabSimprocPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabSimprocPattern___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabSimprocPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_elabSimprocPattern___closed__2 = (const lean_object*)&l_Lean_Elab_elabSimprocPattern___closed__2_value;
static const lean_ctor_object l_Lean_Elab_elabSimprocPattern___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_elabSimprocPattern___closed__3 = (const lean_object*)&l_Lean_Elab_elabSimprocPattern___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Unexpected type for simproc pattern: Expected `"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__0 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__1;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__2 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__3 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__4 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__4_value;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__5 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__5_value;
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkSimprocType___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkSimprocType___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkSimprocType___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__5_value),LEAN_SCALAR_PTR_LITERAL(18, 160, 179, 254, 130, 82, 156, 255)}};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__6 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__6_value;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__7;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__8;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` or `"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__9 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__9_value;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__10;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__11;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DSimproc"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__12 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__12_value;
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkSimprocType___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkSimprocType___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Elab_checkSimprocType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_checkSimprocType___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(119, 227, 62, 233, 71, 149, 243, 160)}};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__13 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__13_value;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__14;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__15;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, but `"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__16 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__16_value;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__17;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__18;
static const lean_string_object l_Lean_Elab_checkSimprocType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_Elab_checkSimprocType___closed__19 = (const lean_object*)&l_Lean_Elab_checkSimprocType___closed__19_value;
static lean_once_cell_t l_Lean_Elab_checkSimprocType___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkSimprocType___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabSimprocPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPattern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simprocPattern"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 202, 22, 200, 44, 153, 152, 252)}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPattern___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabSimprocPattern"};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(50, 105, 236, 199, 86, 84, 106, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(45) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(39) << 1) | 1)),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4_value),((lean_object*)(((size_t)(73) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DiscrTree"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Key"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "star"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 3, 45, 254, 183, 37, 206, 62)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "other"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(138, 126, 131, 170, 147, 7, 98, 166)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(202, 151, 84, 78, 164, 133, 51, 209)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Literal"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(64, 199, 201, 37, 137, 51, 1, 129)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 249, 146, 84, 160, 212, 27)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(191, 195, 92, 248, 246, 94, 216, 42)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "FVarId"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(134, 80, 170, 214, 218, 146, 55, 86)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(246, 212, 153, 136, 172, 214, 179, 96)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(146, 102, 128, 62, 226, 52, 61, 241)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(89, 115, 112, 17, 35, 166, 93, 117)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_0),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 99, 219, 73, 75, 134, 74, 174)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_2),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 101, 12, 51, 56, 72, 50, 91)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_3),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31_value),LEAN_SCALAR_PTR_LITERAL(96, 241, 3, 72, 213, 31, 49, 170)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12_value;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "registerBuiltinSimproc"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13_value;
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "registerBuiltinDSimproc"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "simprocPatternBuiltin"};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Command_elabSimprocPattern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 222, 179, 10, 105, 49, 55, 147)}};
static const lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1 = (const lean_object*)&l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabSimprocPatternBuiltin"};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_checkSimprocType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 136, 86, 100, 30, 5, 77, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)(((size_t)(62) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)(((size_t)(87) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3_value),((lean_object*)(((size_t)(62) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4_value),((lean_object*)(((size_t)(87) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabSimprocPattern___lam__0(lean_object* v_x_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__0___boxed(lean_object* v_x_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_Lean_Elab_elabSimprocPattern___lam__0(v_x_3_);
lean_dec(v_x_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1(lean_object* v_stx_6_, lean_object* v___x_7_, uint8_t v___x_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Term_elabTerm(v_stx_6_, v___x_7_, v___x_8_, v___x_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; uint8_t v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_16_, 1);
v___x_18_ = 0;
v___x_19_ = 0;
v___x_20_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_18_, v___x_19_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v___x_20_, 0);
lean_dec(v_unused_28_);
v___x_22_ = v___x_20_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_dec(v___x_20_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_a_17_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_17_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
lean_dec(v_a_17_);
v_a_29_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_20_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_20_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___lam__1___boxed(lean_object* v_stx_37_, lean_object* v___x_38_, lean_object* v___x_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v___x_369__boxed_47_; lean_object* v_res_48_; 
v___x_369__boxed_47_ = lean_unbox(v___x_39_);
v_res_48_ = l_Lean_Elab_elabSimprocPattern___lam__1(v_stx_37_, v___x_38_, v___x_369__boxed_47_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern(lean_object* v_stx_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v_go_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_69_ = lean_box(0);
v___x_70_ = 1;
v___x_71_ = lean_box(v___x_70_);
v_go_72_ = lean_alloc_closure((void*)(l_Lean_Elab_elabSimprocPattern___lam__1___boxed), 10, 3);
lean_closure_set(v_go_72_, 0, v_stx_63_);
lean_closure_set(v_go_72_, 1, v___x_69_);
lean_closure_set(v_go_72_, 2, v___x_71_);
v___x_73_ = ((lean_object*)(l_Lean_Elab_elabSimprocPattern___closed__2));
v___x_74_ = ((lean_object*)(l_Lean_Elab_elabSimprocPattern___closed__3));
v___x_75_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_go_72_, v___x_73_, v___x_74_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_fst_80_; lean_object* v___x_82_; 
v_fst_80_ = lean_ctor_get(v_a_76_, 0);
lean_inc(v_fst_80_);
lean_dec(v_a_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v_fst_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_fst_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_a_85_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_75_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_75_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocPattern___boxed(lean_object* v_stx_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Elab_elabSimprocPattern(v_stx_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys(lean_object* v_stx_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Elab_elabSimprocPattern(v_stx_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_108_; lean_object* v_config_109_; uint8_t v_trackZetaDelta_110_; lean_object* v_zetaDeltaSet_111_; lean_object* v_lctx_112_; lean_object* v_localInstances_113_; lean_object* v_defEqCtx_x3f_114_; lean_object* v_synthPendingDepth_115_; lean_object* v_customCanUnfoldPredicate_x3f_116_; uint8_t v_univApprox_117_; uint8_t v_inTypeClassResolution_118_; uint8_t v_cacheInferType_119_; uint64_t v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = l_Lean_Meta_simpGlobalConfig;
v_config_109_ = lean_ctor_get(v___x_108_, 0);
v_trackZetaDelta_110_ = lean_ctor_get_uint8(v_a_101_, sizeof(void*)*7);
v_zetaDeltaSet_111_ = lean_ctor_get(v_a_101_, 1);
v_lctx_112_ = lean_ctor_get(v_a_101_, 2);
v_localInstances_113_ = lean_ctor_get(v_a_101_, 3);
v_defEqCtx_x3f_114_ = lean_ctor_get(v_a_101_, 4);
v_synthPendingDepth_115_ = lean_ctor_get(v_a_101_, 5);
v_customCanUnfoldPredicate_x3f_116_ = lean_ctor_get(v_a_101_, 6);
v_univApprox_117_ = lean_ctor_get_uint8(v_a_101_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_118_ = lean_ctor_get_uint8(v_a_101_, sizeof(void*)*7 + 2);
v_cacheInferType_119_ = lean_ctor_get_uint8(v_a_101_, sizeof(void*)*7 + 3);
v___x_120_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_109_);
v___x_121_ = 0;
lean_inc_ref(v_config_109_);
v___x_122_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_122_, 0, v_config_109_);
lean_ctor_set_uint64(v___x_122_, sizeof(void*)*1, v___x_120_);
lean_inc(v_customCanUnfoldPredicate_x3f_116_);
lean_inc(v_synthPendingDepth_115_);
lean_inc(v_defEqCtx_x3f_114_);
lean_inc_ref(v_localInstances_113_);
lean_inc_ref(v_lctx_112_);
lean_inc(v_zetaDeltaSet_111_);
v___x_123_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_zetaDeltaSet_111_);
lean_ctor_set(v___x_123_, 2, v_lctx_112_);
lean_ctor_set(v___x_123_, 3, v_localInstances_113_);
lean_ctor_set(v___x_123_, 4, v_defEqCtx_x3f_114_);
lean_ctor_set(v___x_123_, 5, v_synthPendingDepth_115_);
lean_ctor_set(v___x_123_, 6, v_customCanUnfoldPredicate_x3f_116_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*7, v_trackZetaDelta_110_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*7 + 1, v_univApprox_117_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*7 + 2, v_inTypeClassResolution_118_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*7 + 3, v_cacheInferType_119_);
v___x_124_ = l_Lean_Meta_DiscrTree_mkPath(v_a_107_, v___x_121_, v___x_123_, v_a_102_, v_a_103_, v_a_104_);
lean_dec_ref_known(v___x_123_, 7);
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_106_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_106_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSimprocKeys___boxed(lean_object* v_stx_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Elab_elabSimprocKeys(v_stx_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_140_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1);
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
lean_ctor_set(v___x_146_, 4, v___x_144_);
lean_ctor_set(v___x_146_, 5, v___x_144_);
lean_ctor_set(v___x_146_, 6, v___x_144_);
lean_ctor_set(v___x_146_, 7, v___x_144_);
lean_ctor_set(v___x_146_, 8, v___x_144_);
lean_ctor_set(v___x_146_, 9, v___x_144_);
lean_ctor_set(v___x_146_, 10, v___x_144_);
lean_ctor_set(v___x_146_, 11, v___x_143_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_unsigned_to_nat(32u);
v___x_148_ = lean_mk_empty_array_with_capacity(v___x_147_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_150_ = ((size_t)5ULL);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_unsigned_to_nat(32u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3);
v___x_155_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_151_);
lean_ctor_set(v___x_155_, 3, v___x_151_);
lean_ctor_set_usize(v___x_155_, 4, v___x_150_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_box(1);
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(lean_object* v_msgData_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; lean_object* v_toCold_165_; lean_object* v_env_166_; lean_object* v_options_167_; uint8_t v___x_168_; lean_object* v_env_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_toCold_165_ = lean_ctor_get(v___y_161_, 0);
v_env_166_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_166_);
lean_dec(v___x_164_);
v_options_167_ = lean_ctor_get(v_toCold_165_, 2);
v___x_168_ = 0;
v_env_169_ = l_Lean_Environment_setRecordingDeps(v_env_166_, v___x_168_);
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2);
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5);
lean_inc_ref(v_options_167_);
v___x_172_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_172_, 0, v_env_169_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
lean_ctor_set(v___x_172_, 3, v_options_167_);
v___x_173_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_msgData_160_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___boxed(lean_object* v_msgData_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(v_msgData_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_ref_184_; lean_object* v___x_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_ref_184_ = lean_ctor_get(v___y_181_, 2);
v___x_185_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(v_msg_180_, v___y_181_, v___y_182_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_194_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_inc(v_ref_184_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_ref_184_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg___boxed(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(v_msg_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_200_, lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_toCold_205_; lean_object* v_currRecDepth_206_; lean_object* v_ref_207_; uint16_t v_optionFlags_208_; uint8_t v_suppressElabErrors_209_; uint8_t v_checkDeprecated_210_; uint8_t v_isRecordingDeps_211_; lean_object* v_ref_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_toCold_205_ = lean_ctor_get(v___y_202_, 0);
v_currRecDepth_206_ = lean_ctor_get(v___y_202_, 1);
v_ref_207_ = lean_ctor_get(v___y_202_, 2);
v_optionFlags_208_ = lean_ctor_get_uint16(v___y_202_, sizeof(void*)*3);
v_suppressElabErrors_209_ = lean_ctor_get_uint8(v___y_202_, sizeof(void*)*3 + 2);
v_checkDeprecated_210_ = lean_ctor_get_uint8(v___y_202_, sizeof(void*)*3 + 3);
v_isRecordingDeps_211_ = lean_ctor_get_uint8(v___y_202_, sizeof(void*)*3 + 4);
v_ref_212_ = l_Lean_replaceRef(v_ref_200_, v_ref_207_);
lean_inc(v_currRecDepth_206_);
lean_inc_ref(v_toCold_205_);
v___x_213_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_213_, 0, v_toCold_205_);
lean_ctor_set(v___x_213_, 1, v_currRecDepth_206_);
lean_ctor_set(v___x_213_, 2, v_ref_212_);
lean_ctor_set_uint16(v___x_213_, sizeof(void*)*3, v_optionFlags_208_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*3 + 2, v_suppressElabErrors_209_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*3 + 3, v_checkDeprecated_210_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*3 + 4, v_isRecordingDeps_211_);
v___x_214_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(v_msg_201_, v___x_213_, v___y_203_);
lean_dec_ref_known(v___x_213_, 3);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_215_, lean_object* v_msg_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_215_, v_msg_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v_ref_215_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_242_, lean_object* v_declHint_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_env_248_; uint8_t v___x_249_; 
v___x_246_ = lean_box(0);
v___x_247_ = lean_st_ref_get(v___y_244_);
v_env_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc_ref(v_env_248_);
lean_dec(v___x_247_);
v___x_249_ = l_Lean_Name_isAnonymous(v_declHint_243_);
if (v___x_249_ == 0)
{
uint8_t v_isExporting_250_; 
v_isExporting_250_ = lean_ctor_get_uint8(v_env_248_, sizeof(void*)*13);
if (v_isExporting_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec_ref(v_env_248_);
lean_dec(v_declHint_243_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v_msg_242_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; uint8_t v___x_253_; 
lean_inc_ref(v_env_248_);
v___x_252_ = l_Lean_Environment_setExporting(v_env_248_, v___x_249_);
lean_inc(v_declHint_243_);
lean_inc_ref(v___x_252_);
v___x_253_ = l_Lean_Environment_contains(v___x_252_, v_declHint_243_, v_isExporting_250_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v___x_252_);
lean_dec_ref(v_env_248_);
lean_dec(v_declHint_243_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v_msg_242_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_c_260_; lean_object* v___x_261_; 
v___x_255_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2);
v___x_256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5);
v___x_257_ = l_Lean_Options_empty;
lean_inc_ref(v___x_252_);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v___x_252_);
lean_ctor_set(v___x_258_, 1, v___x_255_);
lean_ctor_set(v___x_258_, 2, v___x_256_);
lean_ctor_set(v___x_258_, 3, v___x_257_);
lean_inc(v_declHint_243_);
v___x_259_ = l_Lean_MessageData_ofConstName(v_declHint_243_, v___x_249_);
v_c_260_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_260_, 0, v___x_258_);
lean_ctor_set(v_c_260_, 1, v___x_259_);
v___x_261_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_252_, v_declHint_243_);
lean_dec_ref(v___x_252_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v_env_248_);
lean_dec(v_declHint_243_);
v___x_262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_c_260_);
v___x_264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_MessageData_note(v___x_265_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v_msg_242_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_303_; 
v_val_269_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_303_ == 0)
{
v___x_271_ = v___x_261_;
v_isShared_272_ = v_isSharedCheck_303_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_val_269_);
lean_dec(v___x_261_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_303_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v_moduleNames_274_; lean_object* v_mod_275_; uint8_t v___x_276_; 
v___x_273_ = l_Lean_Environment_header(v_env_248_);
lean_dec_ref(v_env_248_);
v_moduleNames_274_ = lean_ctor_get(v___x_273_, 4);
lean_inc_ref(v_moduleNames_274_);
lean_dec_ref(v___x_273_);
v_mod_275_ = lean_array_get(v___x_246_, v_moduleNames_274_, v_val_269_);
lean_dec(v_val_269_);
lean_dec_ref(v_moduleNames_274_);
v___x_276_ = l_Lean_isPrivateName(v_declHint_243_);
lean_dec(v_declHint_243_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_c_260_);
v___x_279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_MessageData_ofName(v_mod_275_);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_MessageData_note(v___x_284_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v_msg_242_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 0);
lean_ctor_set(v___x_271_, 0, v___x_286_);
v___x_288_ = v___x_271_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_c_260_);
v___x_292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l_Lean_MessageData_ofName(v_mod_275_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_MessageData_note(v___x_297_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v_msg_242_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 0);
lean_ctor_set(v___x_271_, 0, v___x_299_);
v___x_301_ = v___x_271_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_env_248_);
lean_dec(v_declHint_243_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v_msg_242_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_305_, lean_object* v_declHint_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_305_, v_declHint_306_, v___y_307_);
lean_dec(v___y_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_310_, lean_object* v_declHint_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_325_; 
v___x_315_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_310_, v_declHint_311_, v___y_313_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_325_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = l_Lean_unknownIdentifierMessageTag;
v___x_321_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_326_, lean_object* v_declHint_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_326_, v_declHint_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_332_, lean_object* v_msg_333_, lean_object* v_declHint_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_a_339_; lean_object* v___x_340_; 
v___x_338_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_333_, v_declHint_334_, v___y_335_, v___y_336_);
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_332_, v_a_339_, v___y_335_, v___y_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_341_, lean_object* v_msg_342_, lean_object* v_declHint_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_341_, v_msg_342_, v_declHint_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v_ref_341_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_354_, lean_object* v_constName_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_359_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_360_ = 0;
lean_inc(v_constName_355_);
v___x_361_ = l_Lean_MessageData_ofConstName(v_constName_355_, v___x_360_);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_359_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_354_, v___x_364_, v_constName_355_, v___y_356_, v___y_357_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_366_, lean_object* v_constName_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_366_, v_constName_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v_ref_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(lean_object* v_constName_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_ref_376_; lean_object* v___x_377_; 
v_ref_376_ = lean_ctor_get(v___y_373_, 2);
v___x_377_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_376_, v_constName_372_, v___y_373_, v___y_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(v_constName_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(lean_object* v_constName_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v_env_388_; uint8_t v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_st_ref_get(v___y_385_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___x_389_ = 0;
lean_inc(v_constName_383_);
v___x_390_ = l_Lean_Environment_find_x3f(v_env_388_, v_constName_383_, v___x_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(v_constName_383_, v___y_384_, v___y_385_);
return v___x_391_;
}
else
{
lean_object* v_val_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_constName_383_);
v_val_392_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_390_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_val_392_);
lean_dec(v___x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 0);
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_val_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0___boxed(lean_object* v_constName_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(v_constName_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_404_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__0));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__7(void){
_start:
{
uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = 0;
v___x_418_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__6));
v___x_419_ = l_Lean_MessageData_ofConstName(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__8(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__7, &l_Lean_Elab_checkSimprocType___closed__7_once, _init_l_Lean_Elab_checkSimprocType___closed__7);
v___x_421_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__1, &l_Lean_Elab_checkSimprocType___closed__1_once, _init_l_Lean_Elab_checkSimprocType___closed__1);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__10(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__9));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__11(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__10, &l_Lean_Elab_checkSimprocType___closed__10_once, _init_l_Lean_Elab_checkSimprocType___closed__10);
v___x_427_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__8, &l_Lean_Elab_checkSimprocType___closed__8_once, _init_l_Lean_Elab_checkSimprocType___closed__8);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__14(void){
_start:
{
uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = 0;
v___x_436_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__13));
v___x_437_ = l_Lean_MessageData_ofConstName(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__15(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__14, &l_Lean_Elab_checkSimprocType___closed__14_once, _init_l_Lean_Elab_checkSimprocType___closed__14);
v___x_439_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__11, &l_Lean_Elab_checkSimprocType___closed__11_once, _init_l_Lean_Elab_checkSimprocType___closed__11);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__17(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__16));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__18(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__17, &l_Lean_Elab_checkSimprocType___closed__17_once, _init_l_Lean_Elab_checkSimprocType___closed__17);
v___x_445_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__15, &l_Lean_Elab_checkSimprocType___closed__15_once, _init_l_Lean_Elab_checkSimprocType___closed__15);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Elab_checkSimprocType___closed__20(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__19));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType(lean_object* v_declName_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; 
lean_inc(v_declName_450_);
v___x_454_ = l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(v_declName_450_, v_a_451_, v_a_452_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_500_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_500_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_500_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_500_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_471_; 
v___x_471_ = l_Lean_ConstantInfo_type(v_a_455_);
if (lean_obj_tag(v___x_471_) == 4)
{
lean_object* v_declName_472_; 
v_declName_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_declName_472_);
lean_dec_ref_known(v___x_471_, 2);
if (lean_obj_tag(v_declName_472_) == 1)
{
lean_object* v_pre_473_; 
v_pre_473_ = lean_ctor_get(v_declName_472_, 0);
lean_inc(v_pre_473_);
if (lean_obj_tag(v_pre_473_) == 1)
{
lean_object* v_pre_474_; 
v_pre_474_ = lean_ctor_get(v_pre_473_, 0);
lean_inc(v_pre_474_);
if (lean_obj_tag(v_pre_474_) == 1)
{
lean_object* v_pre_475_; 
v_pre_475_ = lean_ctor_get(v_pre_474_, 0);
lean_inc(v_pre_475_);
if (lean_obj_tag(v_pre_475_) == 1)
{
lean_object* v_pre_476_; 
v_pre_476_ = lean_ctor_get(v_pre_475_, 0);
if (lean_obj_tag(v_pre_476_) == 0)
{
lean_object* v_str_477_; lean_object* v_str_478_; lean_object* v_str_479_; lean_object* v_str_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_str_477_ = lean_ctor_get(v_declName_472_, 1);
lean_inc_ref(v_str_477_);
lean_dec_ref_known(v_declName_472_, 2);
v_str_478_ = lean_ctor_get(v_pre_473_, 1);
lean_inc_ref(v_str_478_);
lean_dec_ref_known(v_pre_473_, 2);
v_str_479_ = lean_ctor_get(v_pre_474_, 1);
lean_inc_ref(v_str_479_);
lean_dec_ref_known(v_pre_474_, 2);
v_str_480_ = lean_ctor_get(v_pre_475_, 1);
lean_inc_ref(v_str_480_);
lean_dec_ref_known(v_pre_475_, 2);
v___x_481_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__2));
v___x_482_ = lean_string_dec_eq(v_str_480_, v___x_481_);
lean_dec_ref(v_str_480_);
if (v___x_482_ == 0)
{
lean_dec_ref(v_str_479_);
lean_dec_ref(v_str_478_);
lean_dec_ref(v_str_477_);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
else
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__3));
v___x_484_ = lean_string_dec_eq(v_str_479_, v___x_483_);
lean_dec_ref(v_str_479_);
if (v___x_484_ == 0)
{
lean_dec_ref(v_str_478_);
lean_dec_ref(v_str_477_);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__4));
v___x_486_ = lean_string_dec_eq(v_str_478_, v___x_485_);
lean_dec_ref(v_str_478_);
if (v___x_486_ == 0)
{
lean_dec_ref(v_str_477_);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
else
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__5));
v___x_488_ = lean_string_dec_eq(v_str_477_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__12));
v___x_490_ = lean_string_dec_eq(v_str_477_, v___x_489_);
lean_dec_ref(v_str_477_);
if (v___x_490_ == 0)
{
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_a_455_);
lean_dec(v_declName_450_);
v___x_491_ = lean_box(v___x_490_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_491_);
v___x_493_ = v___x_457_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec_ref(v_str_477_);
lean_dec(v_a_455_);
lean_dec(v_declName_450_);
v___x_495_ = 0;
v___x_496_ = lean_box(v___x_495_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_496_);
v___x_498_ = v___x_457_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_475_, 2);
lean_dec_ref_known(v_pre_474_, 2);
lean_dec_ref_known(v_pre_473_, 2);
lean_dec_ref_known(v_declName_472_, 2);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
}
else
{
lean_dec(v_pre_475_);
lean_dec_ref_known(v_pre_474_, 2);
lean_dec_ref_known(v_pre_473_, 2);
lean_dec_ref_known(v_declName_472_, 2);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
}
else
{
lean_dec(v_pre_474_);
lean_dec_ref_known(v_pre_473_, 2);
lean_dec_ref_known(v_declName_472_, 2);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
}
else
{
lean_dec_ref_known(v_declName_472_, 2);
lean_dec(v_pre_473_);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
}
else
{
lean_dec(v_declName_472_);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
}
else
{
lean_dec_ref(v___x_471_);
lean_del_object(v___x_457_);
v___y_460_ = v_a_451_;
v___y_461_ = v_a_452_;
goto v___jp_459_;
}
v___jp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__18, &l_Lean_Elab_checkSimprocType___closed__18_once, _init_l_Lean_Elab_checkSimprocType___closed__18);
v___x_463_ = l_Lean_MessageData_ofName(v_declName_450_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_obj_once(&l_Lean_Elab_checkSimprocType___closed__20, &l_Lean_Elab_checkSimprocType___closed__20_once, _init_l_Lean_Elab_checkSimprocType___closed__20);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_ConstantInfo_type(v_a_455_);
lean_dec(v_a_455_);
v___x_468_ = l_Lean_indentExpr(v___x_467_);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_466_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(v___x_469_, v___y_460_, v___y_461_);
return v___x_470_;
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_declName_450_);
v_a_501_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_454_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_454_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkSimprocType___boxed(lean_object* v_declName_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_checkSimprocType(v_declName_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1(lean_object* v_00_u03b1_514_, lean_object* v_msg_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(v_msg_515_, v___y_516_, v___y_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___boxed(lean_object* v_00_u03b1_520_, lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1(v_00_u03b1_520_, v_msg_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0(lean_object* v_00_u03b1_526_, lean_object* v_constName_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(v_constName_527_, v___y_528_, v___y_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_532_, lean_object* v_constName_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0(v_00_u03b1_532_, v_constName_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_538_, lean_object* v_ref_539_, lean_object* v_constName_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_539_, v_constName_540_, v___y_541_, v___y_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_545_, lean_object* v_ref_546_, lean_object* v_constName_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_545_, v_ref_546_, v_constName_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v_ref_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_552_, lean_object* v_ref_553_, lean_object* v_msg_554_, lean_object* v_declHint_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_553_, v_msg_554_, v_declHint_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_560_, lean_object* v_ref_561_, lean_object* v_msg_562_, lean_object* v_declHint_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_560_, v_ref_561_, v_msg_562_, v_declHint_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_ref_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_568_, lean_object* v_declHint_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_568_, v_declHint_569_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_574_, lean_object* v_declHint_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_574_, v_declHint_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_580_, lean_object* v_ref_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_581_, v_msg_582_, v___y_583_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_587_, lean_object* v_ref_588_, lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_587_, v_ref_588_, v_msg_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v_ref_588_);
return v_res_593_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_box(0);
v___x_595_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg(){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___boxed(lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0(lean_object* v_00_u03b1_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___boxed(lean_object* v_00_u03b1_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0(v_00_u03b1_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0(lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_realizeGlobalConstNoOverload(v___x_612_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_n(v_a_622_, 2);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = l_Lean_Elab_checkSimprocType(v_a_622_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_624_; 
lean_dec_ref_known(v___x_623_, 1);
v___x_624_ = l_Lean_Elab_elabSimprocKeys(v___x_613_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = l_Lean_Meta_Simp_registerSimproc(v_a_622_, v_a_625_, v___y_618_, v___y_619_);
return v___x_626_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_622_);
v_a_627_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_624_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_624_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_622_);
lean_dec(v___x_613_);
v_a_635_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_623_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_623_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v___x_613_);
v_a_643_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_621_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_621_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Elab_Command_elabSimprocPattern___lam__0(v___x_651_, v___x_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern(lean_object* v_stx_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPattern___closed__2));
lean_inc(v_stx_667_);
v___x_672_ = l_Lean_Syntax_isOfKind(v_stx_667_, v___x_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec(v_stx_667_);
v___x_673_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
return v___x_673_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___f_678_; lean_object* v___x_679_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = l_Lean_Syntax_getArg(v_stx_667_, v___x_674_);
v___x_676_ = lean_unsigned_to_nat(3u);
v___x_677_ = l_Lean_Syntax_getArg(v_stx_667_, v___x_676_);
lean_dec(v_stx_667_);
v___f_678_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed), 9, 2);
lean_closure_set(v___f_678_, 0, v___x_677_);
lean_closure_set(v___f_678_, 1, v___x_675_);
v___x_679_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_678_, v_a_668_, v_a_669_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPattern___boxed(lean_object* v_stx_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_Command_elabSimprocPattern(v_stx_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1(){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_694_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_695_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPattern___closed__2));
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3));
v___x_697_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPattern___boxed), 4, 0);
v___x_698_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_694_, v___x_695_, v___x_696_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___boxed(lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1();
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3(){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3));
v___x_728_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6));
v___x_729_ = l_Lean_addBuiltinDeclarationRanges(v___x_727_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___boxed(lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3();
return v_res_731_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_box(0);
v___x_742_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3));
v___x_743_ = l_Lean_mkConst(v___x_742_, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_box(0);
v___x_752_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6));
v___x_753_ = l_Lean_mkConst(v___x_752_, v___x_751_);
return v___x_753_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_box(0);
v___x_762_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9));
v___x_763_ = l_Lean_mkConst(v___x_762_, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_box(0);
v___x_771_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13));
v___x_772_ = l_Lean_mkConst(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_box(0);
v___x_779_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16));
v___x_780_ = l_Lean_mkConst(v___x_779_, v___x_778_);
return v___x_780_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = lean_box(0);
v___x_789_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19));
v___x_790_ = l_Lean_mkConst(v___x_789_, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_box(0);
v___x_798_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23));
v___x_799_ = l_Lean_mkConst(v___x_798_, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_box(0);
v___x_808_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26));
v___x_809_ = l_Lean_mkConst(v___x_808_, v___x_807_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_box(0);
v___x_818_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29));
v___x_819_ = l_Lean_mkConst(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_box(0);
v___x_828_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32));
v___x_829_ = l_Lean_mkConst(v___x_828_, v___x_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(lean_object* v_nilFn_830_, lean_object* v_consFn_831_, lean_object* v_x_832_){
_start:
{
if (lean_obj_tag(v_x_832_) == 0)
{
lean_dec_ref(v_consFn_831_);
lean_inc_ref(v_nilFn_830_);
return v_nilFn_830_;
}
else
{
lean_object* v_head_833_; lean_object* v_tail_834_; lean_object* v___y_836_; 
v_head_833_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_head_833_);
v_tail_834_ = lean_ctor_get(v_x_832_, 1);
lean_inc(v_tail_834_);
lean_dec_ref_known(v_x_832_, 2);
switch(lean_obj_tag(v_head_833_))
{
case 0:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4);
v___y_836_ = v___x_839_;
goto v___jp_835_;
}
case 1:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7);
v___y_836_ = v___x_840_;
goto v___jp_835_;
}
case 2:
{
lean_object* v_a_841_; lean_object* v___x_842_; 
v_a_841_ = lean_ctor_get(v_head_833_, 0);
lean_inc_ref(v_a_841_);
lean_dec_ref_known(v_head_833_, 1);
v___x_842_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10);
if (lean_obj_tag(v_a_841_) == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_843_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14);
v___x_844_ = l_Lean_Expr_lit___override(v_a_841_);
v___x_845_ = l_Lean_Expr_app___override(v___x_843_, v___x_844_);
v___x_846_ = l_Lean_Expr_app___override(v___x_842_, v___x_845_);
v___y_836_ = v___x_846_;
goto v___jp_835_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17);
v___x_848_ = l_Lean_Expr_lit___override(v_a_841_);
v___x_849_ = l_Lean_Expr_app___override(v___x_847_, v___x_848_);
v___x_850_ = l_Lean_Expr_app___override(v___x_842_, v___x_849_);
v___y_836_ = v___x_850_;
goto v___jp_835_;
}
}
case 3:
{
lean_object* v_a_851_; lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_a_851_ = lean_ctor_get(v_head_833_, 0);
lean_inc(v_a_851_);
v_a_852_ = lean_ctor_get(v_head_833_, 1);
lean_inc(v_a_852_);
lean_dec_ref_known(v_head_833_, 2);
v___x_853_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20);
v___x_854_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24);
v___x_855_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_851_);
v___x_856_ = l_Lean_Expr_app___override(v___x_854_, v___x_855_);
v___x_857_ = l_Lean_mkNatLit(v_a_852_);
v___x_858_ = l_Lean_mkAppB(v___x_853_, v___x_856_, v___x_857_);
v___y_836_ = v___x_858_;
goto v___jp_835_;
}
case 4:
{
lean_object* v_a_859_; lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_859_ = lean_ctor_get(v_head_833_, 0);
lean_inc(v_a_859_);
v_a_860_ = lean_ctor_get(v_head_833_, 1);
lean_inc(v_a_860_);
lean_dec_ref_known(v_head_833_, 2);
v___x_861_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27);
v___x_862_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_859_);
v___x_863_ = l_Lean_mkNatLit(v_a_860_);
v___x_864_ = l_Lean_mkAppB(v___x_861_, v___x_862_, v___x_863_);
v___y_836_ = v___x_864_;
goto v___jp_835_;
}
case 5:
{
lean_object* v___x_865_; 
v___x_865_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30);
v___y_836_ = v___x_865_;
goto v___jp_835_;
}
default: 
{
lean_object* v_a_866_; lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_a_866_ = lean_ctor_get(v_head_833_, 0);
lean_inc(v_a_866_);
v_a_867_ = lean_ctor_get(v_head_833_, 1);
lean_inc(v_a_867_);
v_a_868_ = lean_ctor_get(v_head_833_, 2);
lean_inc(v_a_868_);
lean_dec_ref_known(v_head_833_, 3);
v___x_869_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33);
v___x_870_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_866_);
v___x_871_ = l_Lean_mkNatLit(v_a_867_);
v___x_872_ = l_Lean_mkNatLit(v_a_868_);
v___x_873_ = l_Lean_mkApp3(v___x_869_, v___x_870_, v___x_871_, v___x_872_);
v___y_836_ = v___x_873_;
goto v___jp_835_;
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_inc_ref(v_consFn_831_);
v___x_837_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(v_nilFn_830_, v_consFn_831_, v_tail_834_);
v___x_838_ = l_Lean_mkAppB(v_consFn_831_, v___y_836_, v___x_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(lean_object* v_nilFn_874_, lean_object* v_consFn_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(v_nilFn_874_, v_consFn_875_, v_x_876_);
lean_dec_ref(v_nilFn_874_);
return v_res_877_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3));
v___x_887_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2));
v___x_888_ = l_Lean_mkConst(v___x_887_, v___x_886_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3));
v___x_894_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6));
v___x_895_ = l_Lean_mkConst(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3));
v___x_901_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9));
v___x_902_ = l_Lean_mkConst(v___x_901_, v___x_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_realizeGlobalConstNoOverload(v___x_908_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_n(v_a_920_, 2);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = l_Lean_Elab_checkSimprocType(v_a_920_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = l_Lean_Elab_elabSimprocKeys(v___x_909_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___y_926_; uint8_t v___x_962_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_962_ = lean_unbox(v_a_922_);
lean_dec(v_a_922_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_963_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__3));
v___x_964_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__4));
v___x_965_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13));
lean_inc_ref(v___x_910_);
v___x_966_ = l_Lean_Name_mkStr4(v___x_910_, v___x_963_, v___x_964_, v___x_965_);
v___y_926_ = v___x_966_;
goto v___jp_925_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__3));
v___x_968_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__4));
v___x_969_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14));
lean_inc_ref(v___x_910_);
v___x_970_ = l_Lean_Name_mkStr4(v___x_910_, v___x_967_, v___x_968_, v___x_969_);
v___y_926_ = v___x_970_;
goto v___jp_925_;
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_nil_937_; lean_object* v___x_938_; lean_object* v_cons_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_927_ = lean_box(0);
v___x_928_ = l_Lean_mkConst(v___y_926_, v___x_927_);
lean_inc_n(v_a_920_, 2);
v___x_929_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_920_);
v___x_930_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__3));
v___x_931_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0));
v___x_932_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1));
v___x_933_ = l_Lean_Name_mkStr4(v___x_910_, v___x_930_, v___x_931_, v___x_932_);
v___x_934_ = l_Lean_mkConst(v___x_933_, v___x_927_);
v___x_935_ = lean_obj_once(&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4, &l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4_once, _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4);
v___x_936_ = lean_obj_once(&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7, &l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7_once, _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7);
lean_inc_ref_n(v___x_934_, 2);
v_nil_937_ = l_Lean_Expr_app___override(v___x_936_, v___x_934_);
v___x_938_ = lean_obj_once(&l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10, &l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10_once, _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10);
v_cons_939_ = l_Lean_Expr_app___override(v___x_938_, v___x_934_);
v___x_940_ = lean_array_to_list(v_a_924_);
v___x_941_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(v_nil_937_, v_cons_939_, v___x_940_);
lean_dec_ref(v_nil_937_);
v___x_942_ = l_Lean_mkAppB(v___x_935_, v___x_934_, v___x_941_);
v___x_943_ = l_Lean_mkConst(v_a_920_, v___x_927_);
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_911_);
v___x_945_ = lean_array_push(v___x_944_, v___x_929_);
v___x_946_ = lean_array_push(v___x_945_, v___x_942_);
v___x_947_ = lean_array_push(v___x_946_, v___x_943_);
v___x_948_ = l_Lean_mkAppN(v___x_928_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12));
v___x_950_ = l_Lean_Name_append(v_a_920_, v___x_949_);
v___x_951_ = l_Lean_Core_mkFreshUserName(v___x_950_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = l_Lean_declareBuiltin(v_a_952_, v___x_948_, v___y_916_, v___y_917_);
return v___x_953_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___x_948_);
v_a_954_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_951_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_951_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_a_922_);
lean_dec(v_a_920_);
lean_dec_ref(v___x_910_);
v_a_971_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_923_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_923_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v_a_920_);
lean_dec_ref(v___x_910_);
lean_dec(v___x_909_);
v_a_979_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_921_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_921_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___x_910_);
lean_dec(v___x_909_);
v_a_987_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_919_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_919_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(lean_object* v___x_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v___x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(v___x_995_, v___x_996_, v___x_997_, v___x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___x_998_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin(lean_object* v_stx_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1016_ = ((lean_object*)(l_Lean_Elab_checkSimprocType___closed__2));
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1));
lean_inc(v_stx_1012_);
v___x_1018_ = l_Lean_Syntax_isOfKind(v_stx_1012_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
lean_dec(v_stx_1012_);
v___x_1019_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = l_Lean_Syntax_getArg(v_stx_1012_, v___x_1020_);
v___x_1022_ = lean_unsigned_to_nat(3u);
v___x_1023_ = l_Lean_Syntax_getArg(v_stx_1012_, v___x_1022_);
lean_dec(v_stx_1012_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
lean_closure_set(v___f_1024_, 1, v___x_1021_);
lean_closure_set(v___f_1024_, 2, v___x_1016_);
lean_closure_set(v___f_1024_, 3, v___x_1022_);
v___x_1025_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1024_, v_a_1013_, v_a_1014_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(lean_object* v_stx_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin(v_stx_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1(){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1038_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1));
v___x_1040_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1));
v___x_1041_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed), 4, 0);
v___x_1042_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1038_, v___x_1039_, v___x_1040_, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___boxed(lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1();
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3(){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1));
v___x_1072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6));
v___x_1073_ = l_Lean_addBuiltinDeclarationRanges(v___x_1071_, v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___boxed(lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3();
return v_res_1075_;
}
}
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Simproc(builtin);
}
#ifdef __cplusplus
}
#endif
