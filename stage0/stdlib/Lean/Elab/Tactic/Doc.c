// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: import Lean.DocString public import Lean.Elab.Command public import Lean.Parser.Tactic.Doc
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_withExprHover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic_extension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 145, 122, 23, 135, 199, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Malformed tactic extension command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Missing documentation comment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed 'register_tactic_tag' command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 185, 128, 48, 210, 24, 186)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " — \""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0;
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1_, v___x_2_, v___y_7_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(v___x_11_, v___x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_20_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_21_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v___x_25_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
lean_ctor_set(v___x_26_, 5, v___x_24_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
lean_ctor_set(v___x_26_, 9, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(32u);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4(void){
_start:
{
size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = ((size_t)5ULL);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_unsigned_to_nat(32u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3);
v___x_35_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_31_);
lean_ctor_set(v___x_35_, 3, v___x_31_);
lean_ctor_set_usize(v___x_35_, 4, v___x_30_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_box(1);
v___x_37_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object* v_msgData_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v_scopes_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_opts_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_43_ = lean_st_ref_get(v___y_41_);
v_env_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_st_ref_get(v___y_41_);
v_scopes_46_ = lean_ctor_get(v___x_45_, 2);
lean_inc(v_scopes_46_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_48_ = l_List_head_x21___redArg(v___x_47_, v_scopes_46_);
lean_dec(v_scopes_46_);
v_opts_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_opts_49_);
lean_dec(v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5);
v___x_52_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_52_, 0, v_env_44_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v_opts_49_);
v___x_53_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_msgData_40_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_55_, v___y_56_);
lean_dec(v___y_56_);
return v_res_58_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(1);
v___x_60_ = l_Lean_MessageData_ofFormat(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2));
v___x_65_ = l_Lean_MessageData_ofFormat(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
return v_x_66_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_91_; 
v_head_68_ = lean_ctor_get(v_x_67_, 0);
v_tail_69_ = lean_ctor_get(v_x_67_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_71_ = v_x_67_;
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_tail_69_);
lean_inc(v_head_68_);
lean_dec(v_x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_before_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_89_; 
v_before_73_ = lean_ctor_get(v_head_68_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_head_68_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_head_68_, 1);
lean_dec(v_unused_90_);
v___x_75_ = v_head_68_;
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_before_73_);
lean_dec(v_head_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 7);
lean_ctor_set(v___x_75_, 1, v___x_77_);
lean_ctor_set(v___x_75_, 0, v_x_66_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_x_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_88_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 7);
lean_ctor_set(v___x_71_, 1, v___x_80_);
lean_ctor_set(v___x_71_, 0, v___x_79_);
v___x_82_ = v___x_71_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_87_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = l_Lean_MessageData_ofSyntax(v_before_73_);
v___x_84_ = l_Lean_indentD(v___x_83_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v_x_66_ = v___x_85_;
v_x_67_ = v_tail_69_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object* v_opts_92_, lean_object* v_opt_93_){
_start:
{
lean_object* v_name_94_; lean_object* v_defValue_95_; lean_object* v_map_96_; lean_object* v___x_97_; 
v_name_94_ = lean_ctor_get(v_opt_93_, 0);
v_defValue_95_ = lean_ctor_get(v_opt_93_, 1);
v_map_96_ = lean_ctor_get(v_opts_92_, 0);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_96_, v_name_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v_defValue_95_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_97_, 1);
if (lean_obj_tag(v_val_99_) == 1)
{
uint8_t v_v_100_; 
v_v_100_ = lean_ctor_get_uint8(v_val_99_, 0);
lean_dec_ref_known(v_val_99_, 0);
return v_v_100_;
}
else
{
uint8_t v___x_101_; 
lean_dec(v_val_99_);
v___x_101_ = lean_unbox(v_defValue_95_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_102_, lean_object* v_opt_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_102_, v_opt_103_);
lean_dec_ref(v_opt_103_);
lean_dec_ref(v_opts_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1));
v___x_110_ = l_Lean_MessageData_ofFormat(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object* v_msgData_111_, lean_object* v_macroStack_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_scopes_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_opts_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_scopes_116_ = lean_ctor_get(v___x_115_, 2);
lean_inc(v_scopes_116_);
lean_dec(v___x_115_);
v___x_117_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_118_ = l_List_head_x21___redArg(v___x_117_, v_scopes_116_);
lean_dec(v_scopes_116_);
v_opts_119_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_opts_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_Elab_pp_macroStack;
v___x_121_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_119_, v___x_120_);
lean_dec_ref(v_opts_119_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_macroStack_112_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v_msgData_111_);
return v___x_122_;
}
else
{
if (lean_obj_tag(v_macroStack_112_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v_msgData_111_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_after_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_140_; 
v_head_124_ = lean_ctor_get(v_macroStack_112_, 0);
lean_inc(v_head_124_);
v_after_125_ = lean_ctor_get(v_head_124_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_head_124_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_head_124_, 0);
lean_dec(v_unused_141_);
v___x_127_ = v_head_124_;
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_after_125_);
lean_dec(v_head_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 7);
lean_ctor_set(v___x_127_, 1, v___x_129_);
lean_ctor_set(v___x_127_, 0, v_msgData_111_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_msgData_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_139_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_msgData_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2);
v___x_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_MessageData_ofSyntax(v_after_125_);
v___x_135_ = l_Lean_indentD(v___x_134_);
v_msgData_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_136_, 0, v___x_133_);
lean_ctor_set(v_msgData_136_, 1, v___x_135_);
v___x_137_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(v_msgData_136_, v_macroStack_112_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_142_, lean_object* v_macroStack_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_142_, v_macroStack_143_, v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_Command_getRef___redArg(v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
lean_inc(v_macroStack_153_);
v___x_157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_155_, v_macroStack_153_, v___y_149_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_msg_147_);
v_a_167_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_151_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_151_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object* v_ref_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Command_getRef___redArg(v___y_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currRecDepth_189_; lean_object* v_cmdPos_190_; lean_object* v_macroStack_191_; lean_object* v_quotContext_x3f_192_; lean_object* v_currMacroScope_193_; lean_object* v_snap_x3f_194_; lean_object* v_cancelTk_x3f_195_; uint8_t v_suppressElabErrors_196_; lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v_fileName_187_ = lean_ctor_get(v___y_182_, 0);
v_fileMap_188_ = lean_ctor_get(v___y_182_, 1);
v_currRecDepth_189_ = lean_ctor_get(v___y_182_, 2);
v_cmdPos_190_ = lean_ctor_get(v___y_182_, 3);
v_macroStack_191_ = lean_ctor_get(v___y_182_, 4);
v_quotContext_x3f_192_ = lean_ctor_get(v___y_182_, 5);
v_currMacroScope_193_ = lean_ctor_get(v___y_182_, 6);
v_snap_x3f_194_ = lean_ctor_get(v___y_182_, 8);
v_cancelTk_x3f_195_ = lean_ctor_get(v___y_182_, 9);
v_suppressElabErrors_196_ = lean_ctor_get_uint8(v___y_182_, sizeof(void*)*10);
v_ref_197_ = l_Lean_replaceRef(v_ref_180_, v_a_186_);
lean_dec(v_a_186_);
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_snap_x3f_194_);
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_x3f_192_);
lean_inc(v_macroStack_191_);
lean_inc(v_cmdPos_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_198_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_198_, 0, v_fileName_187_);
lean_ctor_set(v___x_198_, 1, v_fileMap_188_);
lean_ctor_set(v___x_198_, 2, v_currRecDepth_189_);
lean_ctor_set(v___x_198_, 3, v_cmdPos_190_);
lean_ctor_set(v___x_198_, 4, v_macroStack_191_);
lean_ctor_set(v___x_198_, 5, v_quotContext_x3f_192_);
lean_ctor_set(v___x_198_, 6, v_currMacroScope_193_);
lean_ctor_set(v___x_198_, 7, v_ref_197_);
lean_ctor_set(v___x_198_, 8, v_snap_x3f_194_);
lean_ctor_set(v___x_198_, 9, v_cancelTk_x3f_195_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*10, v_suppressElabErrors_196_);
v___x_199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_181_, v___x_198_, v___y_183_);
lean_dec_ref_known(v___x_198_, 10);
return v___x_199_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_msg_181_);
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object* v_ref_208_, lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_208_, v_msg_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v_ref_208_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
lean_inc(v_x_247_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_247_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_247_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_254_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_253_, v_a_248_, v_a_249_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Lean_Syntax_getArg(v_x_247_, v___x_255_);
lean_inc(v___x_256_);
v___x_257_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_256_);
v___x_259_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v___x_256_);
lean_dec(v_x_247_);
v___x_260_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_260_, v_a_248_, v_a_249_);
return v___x_261_;
}
else
{
lean_object* v_docs_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_docs_262_ = l_Lean_Syntax_getArg(v___x_256_, v___x_255_);
lean_dec(v___x_256_);
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_docs_262_);
v___x_264_ = l_Lean_Syntax_isOfKind(v_docs_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_docs_262_);
lean_dec(v_x_247_);
v___x_265_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_265_, v_a_248_, v_a_249_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = l_Lean_Syntax_getArg(v_x_247_, v___x_267_);
lean_dec(v_x_247_);
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v___x_268_);
v___x_270_ = l_Lean_Syntax_isOfKind(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v___x_271_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_271_, v_a_248_, v_a_249_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
lean_inc(v___x_268_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_274_, 0, v___x_268_);
lean_closure_set(v___f_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_274_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_342_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_342_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_342_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_342_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___y_281_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; 
v___x_329_ = lean_st_ref_get(v_a_249_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
lean_inc(v_a_276_);
v___x_331_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_330_, v_a_276_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_334_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_MessageData_ofConstName(v_val_332_, v___x_257_);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_333_);
v___x_341_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_340_, v_a_248_, v_a_249_);
lean_dec(v___x_268_);
return v___x_341_;
}
else
{
lean_dec(v___x_331_);
v___y_324_ = v_a_248_;
v___y_325_ = v_a_249_;
goto v___jp_323_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v_messages_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_312_; 
v___x_282_ = lean_st_ref_take(v___y_281_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
v_messages_284_ = lean_ctor_get(v___x_282_, 1);
v_scopes_285_ = lean_ctor_get(v___x_282_, 2);
v_usedQuotCtxts_286_ = lean_ctor_get(v___x_282_, 3);
v_nextMacroScope_287_ = lean_ctor_get(v___x_282_, 4);
v_maxRecDepth_288_ = lean_ctor_get(v___x_282_, 5);
v_ngen_289_ = lean_ctor_get(v___x_282_, 6);
v_auxDeclNGen_290_ = lean_ctor_get(v___x_282_, 7);
v_infoState_291_ = lean_ctor_get(v___x_282_, 8);
v_traceState_292_ = lean_ctor_get(v___x_282_, 9);
v_snapshotTasks_293_ = lean_ctor_get(v___x_282_, 10);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_312_ == 0)
{
v___x_295_ = v___x_282_;
v_isShared_296_ = v_isSharedCheck_312_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_snapshotTasks_293_);
lean_inc(v_traceState_292_);
lean_inc(v_infoState_291_);
lean_inc(v_auxDeclNGen_290_);
lean_inc(v_ngen_289_);
lean_inc(v_maxRecDepth_288_);
lean_inc(v_nextMacroScope_287_);
lean_inc(v_usedQuotCtxts_286_);
lean_inc(v_scopes_285_);
lean_inc(v_messages_284_);
lean_inc(v_env_283_);
lean_dec(v___x_282_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_312_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v_toEnvExtension_298_; lean_object* v_asyncMode_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_297_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_298_ = lean_ctor_get(v___x_297_, 0);
v_asyncMode_299_ = lean_ctor_get(v_toEnvExtension_298_, 2);
v___x_300_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_a_276_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_297_, v_env_283_, v___x_301_, v_asyncMode_299_, v___x_302_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_303_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_messages_284_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_311_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_311_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_311_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 10, v_snapshotTasks_293_);
v___x_305_ = v_reuseFailAlloc_311_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = lean_st_ref_set(v___y_281_, v___x_305_);
v___x_307_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_307_);
v___x_309_ = v___x_278_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
v___jp_313_:
{
if (v___y_316_ == 0)
{
lean_dec(v___x_268_);
v___y_281_ = v___y_315_;
goto v___jp_280_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v___x_317_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_318_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_321_, v___y_314_, v___y_315_);
lean_dec(v___x_268_);
return v___x_322_;
}
}
v___jp_323_:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; 
v___x_326_ = lean_st_ref_get(v___y_325_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_327_, v_a_276_);
if (v___x_328_ == 0)
{
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___x_270_;
goto v___jp_313_;
}
else
{
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___x_257_;
goto v___jp_313_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v_a_343_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_275_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_275_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v_cmd_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v___x_256_);
v___x_351_ = lean_unsigned_to_nat(1u);
v_cmd_352_ = l_Lean_Syntax_getArg(v_x_247_, v___x_351_);
lean_dec(v_x_247_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_354_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_352_, v___x_353_, v_a_248_, v_a_249_);
lean_dec(v_cmd_352_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_360_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_ref_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_383_, v_msg_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_389_, lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_389_, v_ref_390_, v_msg_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_ref_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_396_, lean_object* v_macroStack_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_396_, v_macroStack_397_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_402_, lean_object* v_macroStack_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_402_, v_macroStack_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_419_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_423_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_419_, v___x_420_, v___x_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_454_ = l_Lean_addBuiltinDeclarationRanges(v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_456_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_val_472_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_479_);
switch(lean_obj_tag(v___x_480_))
{
case 2:
{
lean_object* v_val_481_; 
lean_dec(v_stx_461_);
v_val_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc_ref(v_val_481_);
lean_dec_ref_known(v___x_480_, 2);
v_val_472_ = v_val_481_;
goto v___jp_471_;
}
case 1:
{
lean_object* v_kind_482_; 
v_kind_482_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_kind_482_);
if (lean_obj_tag(v_kind_482_) == 1)
{
lean_object* v_pre_483_; 
v_pre_483_ = lean_ctor_get(v_kind_482_, 0);
lean_inc(v_pre_483_);
if (lean_obj_tag(v_pre_483_) == 1)
{
lean_object* v_pre_484_; 
v_pre_484_ = lean_ctor_get(v_pre_483_, 0);
lean_inc(v_pre_484_);
if (lean_obj_tag(v_pre_484_) == 1)
{
lean_object* v_pre_485_; 
v_pre_485_ = lean_ctor_get(v_pre_484_, 0);
lean_inc(v_pre_485_);
if (lean_obj_tag(v_pre_485_) == 1)
{
lean_object* v_pre_486_; 
v_pre_486_ = lean_ctor_get(v_pre_485_, 0);
if (lean_obj_tag(v_pre_486_) == 0)
{
lean_object* v_str_487_; lean_object* v_str_488_; lean_object* v_str_489_; lean_object* v_str_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_str_487_ = lean_ctor_get(v_kind_482_, 1);
lean_inc_ref(v_str_487_);
lean_dec_ref_known(v_kind_482_, 2);
v_str_488_ = lean_ctor_get(v_pre_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref_known(v_pre_483_, 2);
v_str_489_ = lean_ctor_get(v_pre_484_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref_known(v_pre_484_, 2);
v_str_490_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref_known(v_pre_485_, 2);
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_492_ = lean_string_dec_eq(v_str_490_, v___x_491_);
lean_dec_ref(v_str_490_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_494_ = lean_string_dec_eq(v_str_489_, v___x_493_);
lean_dec_ref(v_str_489_);
if (v___x_494_ == 0)
{
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_496_ = lean_string_dec_eq(v_str_488_, v___x_495_);
lean_dec_ref(v_str_488_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_str_487_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_498_ = lean_string_dec_eq(v_str_487_, v___x_497_);
lean_dec_ref(v_str_487_);
if (v___x_498_ == 0)
{
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Lean_Syntax_getArg(v___x_480_, v___x_499_);
lean_dec_ref_known(v___x_480_, 3);
if (lean_obj_tag(v___x_500_) == 2)
{
lean_object* v_val_501_; 
lean_dec(v_stx_461_);
v_val_501_ = lean_ctor_get(v___x_500_, 1);
lean_inc_ref(v_val_501_);
lean_dec_ref_known(v___x_500_, 2);
v_val_472_ = v_val_501_;
goto v___jp_471_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v___x_500_);
v___x_502_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_461_);
v___x_503_ = l_Lean_MessageData_ofSyntax(v_stx_461_);
v___x_504_ = l_Lean_indentD(v___x_503_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_502_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_461_, v___x_505_, v___y_462_, v___y_463_);
lean_dec(v_stx_461_);
return v___x_506_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_pre_483_, 2);
lean_dec_ref_known(v_kind_482_, 2);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec(v_pre_485_);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_pre_483_, 2);
lean_dec_ref_known(v_kind_482_, 2);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec_ref_known(v_pre_483_, 2);
lean_dec(v_pre_484_);
lean_dec_ref_known(v_kind_482_, 2);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec_ref_known(v_kind_482_, 2);
lean_dec(v_pre_483_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec(v_kind_482_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
default: 
{
lean_dec(v___x_480_);
goto v___jp_465_;
}
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_461_);
v___x_467_ = l_Lean_MessageData_ofSyntax(v_stx_461_);
v___x_468_ = l_Lean_indentD(v___x_467_);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_466_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_461_, v___x_469_, v___y_462_, v___y_463_);
lean_dec(v_stx_461_);
return v___x_470_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_string_utf8_byte_size(v_val_472_);
v___x_475_ = lean_unsigned_to_nat(2u);
v___x_476_ = lean_nat_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_string_utf8_extract(v_val_472_, v___x_473_, v___x_476_);
lean_dec(v___x_476_);
lean_dec_ref(v_val_472_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v_a_532_; lean_object* v_doc_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_524_);
v___x_600_ = l_Lean_Syntax_isOfKind(v_x_524_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_x_524_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_601_, v_a_525_, v_a_526_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = l_Lean_Syntax_getArg(v_x_524_, v___x_603_);
v___x_605_ = l_Lean_Syntax_isNone(v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_604_);
v___x_607_ = l_Lean_Syntax_matchesNull(v___x_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___x_604_);
lean_dec(v_x_524_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_609_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_608_, v_a_525_, v_a_526_);
return v___x_609_;
}
else
{
lean_object* v_doc_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_doc_610_ = l_Lean_Syntax_getArg(v___x_604_, v___x_603_);
lean_dec(v___x_604_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_610_);
v___x_612_ = l_Lean_Syntax_isOfKind(v_doc_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_doc_610_);
lean_dec(v_x_524_);
v___x_613_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_614_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_613_, v_a_525_, v_a_526_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v_doc_610_);
v_doc_565_ = v___x_615_;
v___y_566_ = v_a_525_;
v___y_567_ = v_a_526_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v___x_616_; 
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_doc_565_ = v___x_616_;
v___y_566_ = v_a_525_;
v___y_567_ = v_a_526_;
goto v___jp_564_;
}
}
v___jp_528_:
{
lean_object* v___x_533_; lean_object* v_env_534_; lean_object* v_messages_535_; lean_object* v_scopes_536_; lean_object* v_usedQuotCtxts_537_; lean_object* v_nextMacroScope_538_; lean_object* v_maxRecDepth_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_infoState_542_; lean_object* v_traceState_543_; lean_object* v_snapshotTasks_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_563_; 
v___x_533_ = lean_st_ref_take(v___y_531_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
v_messages_535_ = lean_ctor_get(v___x_533_, 1);
v_scopes_536_ = lean_ctor_get(v___x_533_, 2);
v_usedQuotCtxts_537_ = lean_ctor_get(v___x_533_, 3);
v_nextMacroScope_538_ = lean_ctor_get(v___x_533_, 4);
v_maxRecDepth_539_ = lean_ctor_get(v___x_533_, 5);
v_ngen_540_ = lean_ctor_get(v___x_533_, 6);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_533_, 7);
v_infoState_542_ = lean_ctor_get(v___x_533_, 8);
v_traceState_543_ = lean_ctor_get(v___x_533_, 9);
v_snapshotTasks_544_ = lean_ctor_get(v___x_533_, 10);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_563_ == 0)
{
v___x_546_ = v___x_533_;
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snapshotTasks_544_);
lean_inc(v_traceState_543_);
lean_inc(v_infoState_542_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_maxRecDepth_539_);
lean_inc(v_nextMacroScope_538_);
lean_inc(v_usedQuotCtxts_537_);
lean_inc(v_scopes_536_);
lean_inc(v_messages_535_);
lean_inc(v_env_534_);
lean_dec(v___x_533_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v_toEnvExtension_549_; lean_object* v_asyncMode_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_548_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_549_ = lean_ctor_get(v___x_548_, 0);
v_asyncMode_550_ = lean_ctor_get(v_toEnvExtension_549_, 2);
v___x_551_ = l_Lean_TSyntax_getId(v___y_529_);
lean_dec(v___y_529_);
v___x_552_ = l_Lean_TSyntax_getString(v___y_530_);
lean_dec(v___y_530_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_532_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_548_, v_env_534_, v___x_554_, v_asyncMode_550_, v___x_555_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_556_);
v___x_558_ = v___x_546_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_messages_535_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_scopes_536_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_usedQuotCtxts_537_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_nextMacroScope_538_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_maxRecDepth_539_);
lean_ctor_set(v_reuseFailAlloc_562_, 6, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 7, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_562_, 8, v_infoState_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 9, v_traceState_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 10, v_snapshotTasks_544_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_st_ref_set(v___y_531_, v___x_558_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
v___jp_564_:
{
lean_object* v___x_568_; lean_object* v_tag_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_568_ = lean_unsigned_to_nat(2u);
v_tag_569_ = l_Lean_Syntax_getArg(v_x_524_, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_569_);
v___x_571_ = l_Lean_Syntax_isOfKind(v_tag_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_tag_569_);
lean_dec(v_doc_565_);
lean_dec(v_x_524_);
v___x_572_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_573_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_572_, v___y_566_, v___y_567_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v_user_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_574_ = lean_unsigned_to_nat(3u);
v_user_575_ = l_Lean_Syntax_getArg(v_x_524_, v___x_574_);
lean_dec(v_x_524_);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_575_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_user_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_user_575_);
lean_dec(v_tag_569_);
lean_dec(v_doc_565_);
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_579_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_578_, v___y_566_, v___y_567_);
return v___x_579_;
}
else
{
if (lean_obj_tag(v_doc_565_) == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
v___y_529_ = v_tag_569_;
v___y_530_ = v_user_575_;
v___y_531_ = v___y_567_;
v_a_532_ = v___x_580_;
goto v___jp_528_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_598_; 
v_val_581_ = lean_ctor_get(v_doc_565_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_doc_565_);
if (v_isSharedCheck_598_ == 0)
{
v___x_583_ = v_doc_565_;
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v_doc_565_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_581_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_a_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v___y_529_ = v_tag_569_;
v___y_530_ = v_user_575_;
v___y_531_ = v___y_567_;
v_a_532_ = v___x_588_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_del_object(v___x_583_);
lean_dec(v_user_575_);
lean_dec(v_tag_569_);
v_a_590_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_585_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_585_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_634_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_630_, v___x_631_, v___x_632_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_665_ = l_Lean_addBuiltinDeclarationRanges(v___x_663_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
return v___x_670_;
}
else
{
lean_dec_ref(v___x_668_);
lean_inc_ref(v_x_669_);
return v_x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_671_, v_x_672_);
lean_dec(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_674_, lean_object* v_k_675_, lean_object* v_t_676_){
_start:
{
if (lean_obj_tag(v_t_676_) == 0)
{
lean_object* v_size_677_; lean_object* v_k_678_; lean_object* v_v_679_; lean_object* v_l_680_; lean_object* v_r_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_1007_; 
v_size_677_ = lean_ctor_get(v_t_676_, 0);
v_k_678_ = lean_ctor_get(v_t_676_, 1);
v_v_679_ = lean_ctor_get(v_t_676_, 2);
v_l_680_ = lean_ctor_get(v_t_676_, 3);
v_r_681_ = lean_ctor_get(v_t_676_, 4);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_t_676_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_683_ = v_t_676_;
v_isShared_684_ = v_isSharedCheck_1007_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_r_681_);
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
lean_inc(v_size_677_);
lean_dec(v_t_676_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_1007_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; 
v___x_685_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_675_, v_k_678_);
switch(v___x_685_)
{
case 0:
{
lean_object* v_impl_686_; lean_object* v___x_687_; 
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
v_impl_686_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_674_, v_k_675_, v_l_680_);
v___x_687_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_678_, v_v_679_, v_impl_686_, v_r_681_);
return v___x_687_;
}
case 1:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_k_678_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_v_679_);
v___x_689_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_674_, v___x_688_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
lean_dec(v_k_675_);
if (lean_obj_tag(v_l_680_) == 0)
{
if (lean_obj_tag(v_r_681_) == 0)
{
lean_object* v_size_690_; lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_l_693_; lean_object* v_r_694_; lean_object* v_size_695_; lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_l_698_; lean_object* v_r_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_size_690_ = lean_ctor_get(v_l_680_, 0);
v_k_691_ = lean_ctor_get(v_l_680_, 1);
v_v_692_ = lean_ctor_get(v_l_680_, 2);
v_l_693_ = lean_ctor_get(v_l_680_, 3);
v_r_694_ = lean_ctor_get(v_l_680_, 4);
lean_inc(v_r_694_);
v_size_695_ = lean_ctor_get(v_r_681_, 0);
v_k_696_ = lean_ctor_get(v_r_681_, 1);
v_v_697_ = lean_ctor_get(v_r_681_, 2);
v_l_698_ = lean_ctor_get(v_r_681_, 3);
lean_inc(v_l_698_);
v_r_699_ = lean_ctor_get(v_r_681_, 4);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_dec_lt(v_size_690_, v_size_695_);
if (v___x_701_ == 0)
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_837_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
v_isSharedCheck_837_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_838_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_842_);
v___x_703_ = v_l_680_;
v_isShared_704_ = v_isSharedCheck_837_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_l_680_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_837_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v_tree_706_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_691_, v_v_692_, v_l_693_, v_r_694_);
v_tree_706_ = lean_ctor_get(v___x_705_, 2);
lean_inc(v_tree_706_);
if (lean_obj_tag(v_tree_706_) == 0)
{
lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_size_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_k_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_707_);
v_v_708_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_708_);
lean_dec_ref(v___x_705_);
v_size_709_ = lean_ctor_get(v_tree_706_, 0);
v___x_710_ = lean_unsigned_to_nat(3u);
v___x_711_ = lean_nat_mul(v___x_710_, v_size_709_);
v___x_712_ = lean_nat_dec_lt(v___x_711_, v_size_695_);
lean_dec(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_l_698_);
v___x_713_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_714_ = lean_nat_add(v___x_713_, v_size_695_);
lean_dec(v___x_713_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_681_);
lean_ctor_set(v___x_703_, 3, v_tree_706_);
lean_ctor_set(v___x_703_, 2, v_v_708_);
lean_ctor_set(v___x_703_, 1, v_k_707_);
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_r_681_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_772_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_772_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_773_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_777_);
v___x_719_ = v_r_681_;
v_isShared_720_ = v_isSharedCheck_772_;
goto v_resetjp_718_;
}
else
{
lean_dec(v_r_681_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_772_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_size_721_; lean_object* v_k_722_; lean_object* v_v_723_; lean_object* v_l_724_; lean_object* v_r_725_; lean_object* v_size_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_size_721_ = lean_ctor_get(v_l_698_, 0);
v_k_722_ = lean_ctor_get(v_l_698_, 1);
v_v_723_ = lean_ctor_get(v_l_698_, 2);
v_l_724_ = lean_ctor_get(v_l_698_, 3);
v_r_725_ = lean_ctor_get(v_l_698_, 4);
v_size_726_ = lean_ctor_get(v_r_699_, 0);
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_nat_mul(v___x_727_, v_size_726_);
v___x_729_ = lean_nat_dec_lt(v_size_721_, v___x_728_);
lean_dec(v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_757_; 
lean_inc(v_r_725_);
lean_inc(v_l_724_);
lean_inc(v_v_723_);
lean_inc(v_k_722_);
v_isSharedCheck_757_ = !lean_is_exclusive(v_l_698_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; 
v_unused_758_ = lean_ctor_get(v_l_698_, 4);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_698_, 3);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_698_, 2);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_698_, 1);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_698_, 0);
lean_dec(v_unused_762_);
v___x_731_ = v_l_698_;
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
else
{
lean_dec(v_l_698_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_747_; 
v___x_733_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_734_ = lean_nat_add(v___x_733_, v_size_695_);
lean_dec(v_size_695_);
if (lean_obj_tag(v_l_724_) == 0)
{
lean_object* v_size_755_; 
v_size_755_ = lean_ctor_get(v_l_724_, 0);
lean_inc(v_size_755_);
v___y_747_ = v_size_755_;
goto v___jp_746_;
}
else
{
lean_object* v___x_756_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___y_747_ = v___x_756_;
goto v___jp_746_;
}
v___jp_735_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_nat_add(v___y_736_, v___y_738_);
lean_dec(v___y_738_);
lean_dec(v___y_736_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 4, v_r_699_);
lean_ctor_set(v___x_731_, 3, v_r_725_);
lean_ctor_set(v___x_731_, 2, v_v_697_);
lean_ctor_set(v___x_731_, 1, v_k_696_);
lean_ctor_set(v___x_731_, 0, v___x_739_);
v___x_741_ = v___x_731_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_r_725_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_r_699_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v___x_741_);
lean_ctor_set(v___x_719_, 3, v___y_737_);
lean_ctor_set(v___x_719_, 2, v_v_723_);
lean_ctor_set(v___x_719_, 1, v_k_722_);
lean_ctor_set(v___x_719_, 0, v___x_734_);
v___x_743_ = v___x_719_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_722_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_723_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___y_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_nat_add(v___x_733_, v___y_747_);
lean_dec(v___y_747_);
lean_dec(v___x_733_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_l_724_);
lean_ctor_set(v___x_703_, 3, v_tree_706_);
lean_ctor_set(v___x_703_, 2, v_v_708_);
lean_ctor_set(v___x_703_, 1, v_k_707_);
lean_ctor_set(v___x_703_, 0, v___x_748_);
v___x_750_ = v___x_703_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_l_724_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_nat_add(v___x_700_, v_size_726_);
if (lean_obj_tag(v_r_725_) == 0)
{
lean_object* v_size_752_; 
v_size_752_ = lean_ctor_get(v_r_725_, 0);
lean_inc(v_size_752_);
v___y_736_ = v___x_751_;
v___y_737_ = v___x_750_;
v___y_738_ = v_size_752_;
goto v___jp_735_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___y_736_ = v___x_751_;
v___y_737_ = v___x_750_;
v___y_738_ = v___x_753_;
goto v___jp_735_;
}
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_763_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_764_ = lean_nat_add(v___x_763_, v_size_695_);
lean_dec(v_size_695_);
v___x_765_ = lean_nat_add(v___x_763_, v_size_721_);
lean_dec(v___x_763_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v_l_698_);
lean_ctor_set(v___x_719_, 3, v_tree_706_);
lean_ctor_set(v___x_719_, 2, v_v_708_);
lean_ctor_set(v___x_719_, 1, v_k_707_);
lean_ctor_set(v___x_719_, 0, v___x_765_);
v___x_767_ = v___x_719_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_698_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_767_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_764_);
v___x_769_ = v___x_703_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_r_699_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_831_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_832_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_836_);
v___x_779_ = v_r_681_;
v_isShared_780_ = v_isSharedCheck_831_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_r_681_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_831_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
if (lean_obj_tag(v_l_698_) == 0)
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_781_; lean_object* v_v_782_; lean_object* v_size_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_k_781_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_781_);
v_v_782_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_782_);
lean_dec_ref(v___x_705_);
v_size_783_ = lean_ctor_get(v_l_698_, 0);
v___x_784_ = lean_nat_add(v___x_700_, v_size_695_);
lean_dec(v_size_695_);
v___x_785_ = lean_nat_add(v___x_700_, v_size_783_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_698_);
lean_ctor_set(v___x_779_, 3, v_tree_706_);
lean_ctor_set(v___x_779_, 2, v_v_782_);
lean_ctor_set(v___x_779_, 1, v_k_781_);
lean_ctor_set(v___x_779_, 0, v___x_785_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_l_698_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_787_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_784_);
v___x_789_ = v___x_703_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_r_699_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_size_695_);
v_k_792_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_792_);
v_v_793_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_793_);
lean_dec_ref(v___x_705_);
v_k_794_ = lean_ctor_get(v_l_698_, 1);
v_v_795_ = lean_ctor_get(v_l_698_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_l_698_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_l_698_, 4);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_698_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_l_698_, 0);
lean_dec(v_unused_812_);
v___x_797_ = v_l_698_;
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_dec(v_l_698_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(3u);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 4, v_r_699_);
lean_ctor_set(v___x_797_, 3, v_r_699_);
lean_ctor_set(v___x_797_, 2, v_v_793_);
lean_ctor_set(v___x_797_, 1, v_k_792_);
lean_ctor_set(v___x_797_, 0, v___x_700_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_r_699_);
v___x_801_ = v_reuseFailAlloc_808_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_699_);
lean_ctor_set(v___x_779_, 0, v___x_700_);
v___x_803_ = v___x_779_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_699_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_803_);
lean_ctor_set(v___x_703_, 3, v___x_801_);
lean_ctor_set(v___x_703_, 2, v_v_795_);
lean_ctor_set(v___x_703_, 1, v_k_794_);
lean_ctor_set(v___x_703_, 0, v___x_799_);
v___x_805_ = v___x_703_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_813_; lean_object* v_v_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_size_695_);
v_k_813_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_813_);
v_v_814_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_814_);
lean_dec_ref(v___x_705_);
v___x_815_ = lean_unsigned_to_nat(3u);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_698_);
lean_ctor_set(v___x_779_, 2, v_v_814_);
lean_ctor_set(v___x_779_, 1, v_k_813_);
lean_ctor_set(v___x_779_, 0, v___x_700_);
v___x_817_ = v___x_779_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_813_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_l_698_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_817_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_815_);
v___x_819_ = v___x_703_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_r_699_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v_k_822_; lean_object* v_v_823_; lean_object* v___x_825_; 
v_k_822_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_822_);
v_v_823_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_823_);
lean_dec_ref(v___x_705_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_699_);
v___x_825_ = v___x_779_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_size_695_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_r_699_);
v___x_825_ = v_reuseFailAlloc_830_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(2u);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_825_);
lean_ctor_set(v___x_703_, 3, v_r_699_);
lean_ctor_set(v___x_703_, 2, v_v_823_);
lean_ctor_set(v___x_703_, 1, v_k_822_);
lean_ctor_set(v___x_703_, 0, v___x_826_);
v___x_828_ = v___x_703_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_822_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_823_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___x_825_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_995_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v_isSharedCheck_995_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_996_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_1000_);
v___x_844_ = v_r_681_;
v_isShared_845_ = v_isSharedCheck_995_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_r_681_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_995_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_tree_847_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_696_, v_v_697_, v_l_698_, v_r_699_);
v_tree_847_ = lean_ctor_get(v___x_846_, 2);
lean_inc(v_tree_847_);
if (lean_obj_tag(v_tree_847_) == 0)
{
lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v_size_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_k_848_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_848_);
v_v_849_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_849_);
lean_dec_ref(v___x_846_);
v_size_850_ = lean_ctor_get(v_tree_847_, 0);
v___x_851_ = lean_unsigned_to_nat(3u);
v___x_852_ = lean_nat_mul(v___x_851_, v_size_850_);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v_size_690_);
lean_dec(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v_r_694_);
v___x_854_ = lean_nat_add(v___x_700_, v_size_690_);
v___x_855_ = lean_nat_add(v___x_854_, v_size_850_);
lean_dec(v___x_854_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_l_680_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_855_);
v___x_857_ = v___x_844_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_tree_847_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_924_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
lean_inc(v_size_690_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_925_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_929_);
v___x_860_ = v_l_680_;
v_isShared_861_ = v_isSharedCheck_924_;
goto v_resetjp_859_;
}
else
{
lean_dec(v_l_680_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_924_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_size_862_; lean_object* v_size_863_; lean_object* v_k_864_; lean_object* v_v_865_; lean_object* v_l_866_; lean_object* v_r_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_size_862_ = lean_ctor_get(v_l_693_, 0);
v_size_863_ = lean_ctor_get(v_r_694_, 0);
v_k_864_ = lean_ctor_get(v_r_694_, 1);
v_v_865_ = lean_ctor_get(v_r_694_, 2);
v_l_866_ = lean_ctor_get(v_r_694_, 3);
v_r_867_ = lean_ctor_get(v_r_694_, 4);
v___x_868_ = lean_unsigned_to_nat(2u);
v___x_869_ = lean_nat_mul(v___x_868_, v_size_862_);
v___x_870_ = lean_nat_dec_lt(v_size_863_, v___x_869_);
lean_dec(v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_908_; 
lean_inc(v_r_867_);
lean_inc(v_l_866_);
lean_inc(v_v_865_);
lean_inc(v_k_864_);
lean_del_object(v___x_860_);
v_isSharedCheck_908_ = !lean_is_exclusive(v_r_694_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_909_ = lean_ctor_get(v_r_694_, 4);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_694_, 3);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_r_694_, 2);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_694_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_r_694_, 0);
lean_dec(v_unused_913_);
v___x_872_ = v_r_694_;
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
else
{
lean_dec(v_r_694_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_896_; lean_object* v___y_898_; 
v___x_874_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_875_ = lean_nat_add(v___x_874_, v_size_850_);
lean_dec(v___x_874_);
v___x_896_ = lean_nat_add(v___x_700_, v_size_862_);
if (lean_obj_tag(v_l_866_) == 0)
{
lean_object* v_size_906_; 
v_size_906_ = lean_ctor_get(v_l_866_, 0);
lean_inc(v_size_906_);
v___y_898_ = v_size_906_;
goto v___jp_897_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = lean_unsigned_to_nat(0u);
v___y_898_ = v___x_907_;
goto v___jp_897_;
}
v___jp_876_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_nat_add(v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_inc_ref(v_tree_847_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 4, v_tree_847_);
lean_ctor_set(v___x_872_, 3, v_r_867_);
lean_ctor_set(v___x_872_, 2, v_v_849_);
lean_ctor_set(v___x_872_, 1, v_k_848_);
lean_ctor_set(v___x_872_, 0, v___x_880_);
v___x_882_ = v___x_872_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_r_867_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_tree_847_);
v___x_882_ = v_reuseFailAlloc_895_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v_tree_847_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_890_ = lean_ctor_get(v_tree_847_, 4);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_tree_847_, 3);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_tree_847_, 2);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_847_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_tree_847_, 0);
lean_dec(v_unused_894_);
v___x_884_ = v_tree_847_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_tree_847_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v___x_882_);
lean_ctor_set(v___x_884_, 3, v___y_877_);
lean_ctor_set(v___x_884_, 2, v_v_865_);
lean_ctor_set(v___x_884_, 1, v_k_864_);
lean_ctor_set(v___x_884_, 0, v___x_875_);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_864_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_865_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___y_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___x_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_nat_add(v___x_896_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___x_896_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_866_);
lean_ctor_set(v___x_844_, 3, v_l_693_);
lean_ctor_set(v___x_844_, 2, v_v_692_);
lean_ctor_set(v___x_844_, 1, v_k_691_);
lean_ctor_set(v___x_844_, 0, v___x_899_);
v___x_901_ = v___x_844_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_l_866_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; 
v___x_902_ = lean_nat_add(v___x_700_, v_size_850_);
if (lean_obj_tag(v_r_867_) == 0)
{
lean_object* v_size_903_; 
v_size_903_ = lean_ctor_get(v_r_867_, 0);
lean_inc(v_size_903_);
v___y_877_ = v___x_901_;
v___y_878_ = v___x_902_;
v___y_879_ = v_size_903_;
goto v___jp_876_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_877_ = v___x_901_;
v___y_878_ = v___x_902_;
v___y_879_ = v___x_904_;
goto v___jp_876_;
}
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_914_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_915_ = lean_nat_add(v___x_914_, v_size_850_);
lean_dec(v___x_914_);
v___x_916_ = lean_nat_add(v___x_700_, v_size_850_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_863_);
lean_dec(v___x_916_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_917_);
v___x_919_ = v___x_844_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_tree_847_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 4, v___x_919_);
lean_ctor_set(v___x_860_, 0, v___x_915_);
v___x_921_ = v___x_860_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_693_) == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_953_; 
lean_inc_ref(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
lean_inc(v_size_690_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_954_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_958_);
v___x_931_ = v_l_680_;
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
else
{
lean_dec(v_l_680_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
if (lean_obj_tag(v_r_694_) == 0)
{
lean_object* v_k_933_; lean_object* v_v_934_; lean_object* v_size_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v_k_933_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_933_);
v_v_934_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_934_);
lean_dec_ref(v___x_846_);
v_size_935_ = lean_ctor_get(v_r_694_, 0);
v___x_936_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_937_ = lean_nat_add(v___x_700_, v_size_935_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_934_);
lean_ctor_set(v___x_844_, 1, v_k_933_);
lean_ctor_set(v___x_844_, 0, v___x_937_);
v___x_939_ = v___x_844_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_k_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_v_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_tree_847_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_939_);
lean_ctor_set(v___x_931_, 0, v___x_936_);
v___x_941_ = v___x_931_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_k_944_; lean_object* v_v_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_size_690_);
v_k_944_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_944_);
v_v_945_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_945_);
lean_dec_ref(v___x_846_);
v___x_946_ = lean_unsigned_to_nat(3u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_694_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_945_);
lean_ctor_set(v___x_844_, 1, v_k_944_);
lean_ctor_set(v___x_844_, 0, v___x_700_);
v___x_948_ = v___x_844_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_r_694_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_948_);
lean_ctor_set(v___x_931_, 0, v___x_946_);
v___x_950_ = v___x_931_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_694_) == 0)
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; 
v_unused_984_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_988_);
v___x_960_ = v_l_680_;
v_isShared_961_ = v_isSharedCheck_983_;
goto v_resetjp_959_;
}
else
{
lean_dec(v_l_680_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_983_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v_k_964_; lean_object* v_v_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_979_; 
v_k_962_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_962_);
v_v_963_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_963_);
lean_dec_ref(v___x_846_);
v_k_964_ = lean_ctor_get(v_r_694_, 1);
v_v_965_ = lean_ctor_get(v_r_694_, 2);
v_isSharedCheck_979_ = !lean_is_exclusive(v_r_694_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; 
v_unused_980_ = lean_ctor_get(v_r_694_, 4);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_r_694_, 3);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_r_694_, 0);
lean_dec(v_unused_982_);
v___x_967_ = v_r_694_;
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_v_965_);
lean_inc(v_k_964_);
lean_dec(v_r_694_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(3u);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v_l_693_);
lean_ctor_set(v___x_967_, 3, v_l_693_);
lean_ctor_set(v___x_967_, 2, v_v_692_);
lean_ctor_set(v___x_967_, 1, v_k_691_);
lean_ctor_set(v___x_967_, 0, v___x_700_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_l_693_);
v___x_971_ = v_reuseFailAlloc_978_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_693_);
lean_ctor_set(v___x_844_, 3, v_l_693_);
lean_ctor_set(v___x_844_, 2, v_v_963_);
lean_ctor_set(v___x_844_, 1, v_k_962_);
lean_ctor_set(v___x_844_, 0, v___x_700_);
v___x_973_ = v___x_844_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_l_693_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v___x_973_);
lean_ctor_set(v___x_960_, 3, v___x_971_);
lean_ctor_set(v___x_960_, 2, v_v_965_);
lean_ctor_set(v___x_960_, 1, v_k_964_);
lean_ctor_set(v___x_960_, 0, v___x_969_);
v___x_975_ = v___x_960_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
else
{
lean_object* v_k_989_; lean_object* v_v_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v_k_989_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_989_);
v_v_990_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_990_);
lean_dec_ref(v___x_846_);
v___x_991_ = lean_unsigned_to_nat(2u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_694_);
lean_ctor_set(v___x_844_, 3, v_l_680_);
lean_ctor_set(v___x_844_, 2, v_v_990_);
lean_ctor_set(v___x_844_, 1, v_k_989_);
lean_ctor_set(v___x_844_, 0, v___x_991_);
v___x_993_ = v___x_844_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_r_694_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
else
{
return v_l_680_;
}
}
else
{
return v_r_681_;
}
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1003_; 
v_val_1001_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_689_, 1);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v_val_1001_);
lean_ctor_set(v___x_683_, 1, v_k_675_);
v___x_1003_ = v___x_683_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_size_677_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_675_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_val_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_r_681_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
default: 
{
lean_object* v_impl_1005_; lean_object* v___x_1006_; 
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
v_impl_1005_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_674_, v_k_675_, v_r_681_);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_678_, v_v_679_, v_l_680_, v_impl_1005_);
return v___x_1006_;
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_674_, v___x_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec(v_k_675_);
return v_t_676_;
}
else
{
lean_object* v_val_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_val_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_k_675_);
lean_ctor_set(v___x_1012_, 2, v_val_1010_);
lean_ctor_set(v___x_1012_, 3, v_t_676_);
lean_ctor_set(v___x_1012_, 4, v_t_676_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1013_, lean_object* v_i_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_keys_1013_);
v___x_1017_ = lean_nat_dec_lt(v_i_1014_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_i_1014_);
return v___x_1017_;
}
else
{
lean_object* v_k_x27_1018_; uint8_t v___x_1019_; 
v_k_x27_1018_ = lean_array_fget_borrowed(v_keys_1013_, v_i_1014_);
v___x_1019_ = lean_name_eq(v_k_1015_, v_k_x27_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1014_, v___x_1020_);
lean_dec(v_i_1014_);
v_i_1014_ = v___x_1021_;
goto _start;
}
else
{
lean_dec(v_i_1014_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1023_, v_i_1024_, v_k_1025_);
lean_dec(v_k_1025_);
lean_dec_ref(v_keys_1023_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; 
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_shift_left(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; 
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0);
v___x_1033_ = lean_usize_sub(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1034_, size_t v_x_1035_, lean_object* v_x_1036_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v_es_1037_; lean_object* v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v_j_1042_; lean_object* v___x_1043_; 
v_es_1037_ = lean_ctor_get(v_x_1034_, 0);
v___x_1038_ = lean_box(2);
v___x_1039_ = ((size_t)5ULL);
v___x_1040_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1041_ = lean_usize_land(v_x_1035_, v___x_1040_);
v_j_1042_ = lean_usize_to_nat(v___x_1041_);
v___x_1043_ = lean_array_get_borrowed(v___x_1038_, v_es_1037_, v_j_1042_);
lean_dec(v_j_1042_);
switch(lean_obj_tag(v___x_1043_))
{
case 0:
{
lean_object* v_key_1044_; uint8_t v___x_1045_; 
v_key_1044_ = lean_ctor_get(v___x_1043_, 0);
v___x_1045_ = lean_name_eq(v_x_1036_, v_key_1044_);
return v___x_1045_;
}
case 1:
{
lean_object* v_node_1046_; size_t v___x_1047_; 
v_node_1046_ = lean_ctor_get(v___x_1043_, 0);
v___x_1047_ = lean_usize_shift_right(v_x_1035_, v___x_1039_);
v_x_1034_ = v_node_1046_;
v_x_1035_ = v___x_1047_;
goto _start;
}
default: 
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
return v___x_1049_;
}
}
}
else
{
lean_object* v_ks_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_ks_1050_ = lean_ctor_get(v_x_1034_, 0);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1050_, v___x_1051_, v_x_1036_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
size_t v_x_4174__boxed_1056_; uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_x_4174__boxed_1056_ = lean_unbox_usize(v_x_1054_);
lean_dec(v_x_1054_);
v_res_1057_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1053_, v_x_4174__boxed_1056_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec_ref(v_x_1053_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1059_; uint64_t v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1723u);
v___x_1060_ = lean_uint64_of_nat(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint64_t v___y_1064_; 
if (lean_obj_tag(v_x_1062_) == 0)
{
uint64_t v___x_1067_; 
v___x_1067_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1064_ = v___x_1067_;
goto v___jp_1063_;
}
else
{
uint64_t v_hash_1068_; 
v_hash_1068_ = lean_ctor_get_uint64(v_x_1062_, sizeof(void*)*2);
v___y_1064_ = v_hash_1068_;
goto v___jp_1063_;
}
v___jp_1063_:
{
size_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_uint64_to_usize(v___y_1064_);
v___x_1066_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1061_, v___x_1065_, v_x_1062_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1069_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_x_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1073_, lean_object* v_a_1074_, uint8_t v___x_1075_, lean_object* v_x_1076_, lean_object* v_____s_1077_){
_start:
{
lean_object* v_fst_1078_; lean_object* v_kinds_1079_; uint8_t v___x_1080_; 
v_fst_1078_ = lean_ctor_get(v_x_1076_, 0);
lean_inc(v_fst_1078_);
lean_dec_ref(v_x_1076_);
v_kinds_1079_ = lean_ctor_get(v_tactics_1073_, 1);
v___x_1080_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1079_, v_fst_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_fst_1078_);
lean_dec(v_a_1074_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_____s_1077_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_Name_toString(v_a_1074_, v___x_1075_);
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1082_, v_fst_1078_, v_____s_1077_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1085_, lean_object* v_a_1086_, lean_object* v___x_1087_, lean_object* v_x_1088_, lean_object* v_____s_1089_){
_start:
{
uint8_t v___x_4242__boxed_1090_; lean_object* v_res_1091_; 
v___x_4242__boxed_1090_ = lean_unbox(v___x_1087_);
v_res_1091_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1085_, v_a_1086_, v___x_4242__boxed_1090_, v_x_1088_, v_____s_1089_);
lean_dec_ref(v_tactics_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1092_, lean_object* v_keys_1093_, lean_object* v_vals_1094_, lean_object* v_i_1095_, lean_object* v_acc_1096_){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_array_get_size(v_keys_1093_);
v___x_1098_ = lean_nat_dec_lt(v_i_1095_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_i_1095_);
lean_dec_ref(v_f_1092_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_acc_1096_);
return v___x_1099_;
}
else
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v___x_1102_; 
v_k_1100_ = lean_array_fget_borrowed(v_keys_1093_, v_i_1095_);
v_v_1101_ = lean_array_fget_borrowed(v_vals_1094_, v_i_1095_);
lean_inc_ref(v_f_1092_);
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
v___x_1102_ = lean_apply_3(v_f_1092_, v_acc_1096_, v_k_1100_, v_v_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec(v_i_1095_);
lean_dec_ref(v_f_1092_);
return v___x_1102_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_i_1095_, v___x_1104_);
lean_dec(v_i_1095_);
v_i_1095_ = v___x_1105_;
v_acc_1096_ = v_a_1103_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1107_, lean_object* v_keys_1108_, lean_object* v_vals_1109_, lean_object* v_i_1110_, lean_object* v_acc_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1107_, v_keys_1108_, v_vals_1109_, v_i_1110_, v_acc_1111_);
lean_dec_ref(v_vals_1109_);
lean_dec_ref(v_keys_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
lean_object* v_es_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1136_; 
v_es_1116_ = lean_ctor_get(v_x_1114_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1114_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1118_ = v_x_1114_;
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_es_1116_);
lean_dec(v_x_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_get_size(v_es_1116_);
v___x_1122_ = lean_nat_dec_lt(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v_es_1116_);
lean_dec_ref(v_f_1113_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v_x_1115_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_x_1115_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_nat_dec_le(v___x_1121_, v___x_1121_);
if (v___x_1126_ == 0)
{
if (v___x_1122_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_es_1116_);
lean_dec_ref(v_f_1113_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v_x_1115_);
v___x_1128_ = v___x_1118_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1115_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1118_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = lean_usize_of_nat(v___x_1121_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1113_, v_es_1116_, v___x_1130_, v___x_1131_, v_x_1115_);
lean_dec_ref(v_es_1116_);
return v___x_1132_;
}
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1118_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_of_nat(v___x_1121_);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1113_, v_es_1116_, v___x_1133_, v___x_1134_, v_x_1115_);
lean_dec_ref(v_es_1116_);
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_ks_1137_; lean_object* v_vs_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_ks_1137_ = lean_ctor_get(v_x_1114_, 0);
lean_inc_ref(v_ks_1137_);
v_vs_1138_ = lean_ctor_get(v_x_1114_, 1);
lean_inc_ref(v_vs_1138_);
lean_dec_ref_known(v_x_1114_, 2);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1113_, v_ks_1137_, v_vs_1138_, v___x_1139_, v_x_1115_);
lean_dec_ref(v_vs_1138_);
lean_dec_ref(v_ks_1137_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1141_, lean_object* v_as_1142_, size_t v_i_1143_, size_t v_stop_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_a_1147_; lean_object* v___y_1152_; uint8_t v___x_1154_; 
v___x_1154_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_array_uget_borrowed(v_as_1142_, v_i_1143_);
switch(lean_obj_tag(v___x_1155_))
{
case 0:
{
lean_object* v_key_1156_; lean_object* v_val_1157_; lean_object* v___x_1158_; 
v_key_1156_ = lean_ctor_get(v___x_1155_, 0);
v_val_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc_ref(v_f_1141_);
lean_inc(v_val_1157_);
lean_inc(v_key_1156_);
v___x_1158_ = lean_apply_3(v_f_1141_, v_b_1145_, v_key_1156_, v_val_1157_);
v___y_1152_ = v___x_1158_;
goto v___jp_1151_;
}
case 1:
{
lean_object* v_node_1159_; lean_object* v___x_1160_; 
v_node_1159_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_node_1159_);
lean_inc_ref(v_f_1141_);
v___x_1160_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1141_, v_node_1159_, v_b_1145_);
v___y_1152_ = v___x_1160_;
goto v___jp_1151_;
}
default: 
{
v_a_1147_ = v_b_1145_;
goto v___jp_1146_;
}
}
}
else
{
lean_object* v___x_1161_; 
lean_dec_ref(v_f_1141_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1145_);
return v___x_1161_;
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1143_, v___x_1148_);
v_i_1143_ = v___x_1149_;
v_b_1145_ = v_a_1147_;
goto _start;
}
v___jp_1151_:
{
if (lean_obj_tag(v___y_1152_) == 0)
{
lean_dec_ref(v_f_1141_);
return v___y_1152_;
}
else
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___y_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___y_1152_, 1);
v_a_1147_ = v_a_1153_;
goto v___jp_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1162_, lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_stop_1165_, lean_object* v_b_1166_){
_start:
{
size_t v_i_boxed_1167_; size_t v_stop_boxed_1168_; lean_object* v_res_1169_; 
v_i_boxed_1167_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_stop_boxed_1168_ = lean_unbox_usize(v_stop_1165_);
lean_dec(v_stop_1165_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1162_, v_as_1163_, v_i_boxed_1167_, v_stop_boxed_1168_, v_b_1166_);
lean_dec_ref(v_as_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1170_, lean_object* v_s_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1172_);
lean_ctor_set(v___x_1174_, 1, v_b_1173_);
v___x_1175_ = lean_apply_2(v_f_1170_, v___x_1174_, v_s_1171_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_a_1184_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1175_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1175_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1192_, lean_object* v_init_1193_, lean_object* v_f_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v_a_1197_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1195_, 0, v_f_1194_);
lean_inc_ref(v_map_1192_);
v___x_1196_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1195_, v_map_1192_, v_init_1193_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
return v_a_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1198_, lean_object* v_init_1199_, lean_object* v_f_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1198_, v_init_1199_, v_f_1200_);
lean_dec_ref(v_map_1198_);
return v_res_1201_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1202_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1205_, lean_object* v_a_1206_, uint8_t v___x_1207_, lean_object* v_as_x27_1208_, lean_object* v_b_1209_){
_start:
{
if (lean_obj_tag(v_as_x27_1208_) == 0)
{
lean_dec(v_a_1206_);
lean_dec_ref(v_tactics_1205_);
return v_b_1209_;
}
else
{
lean_object* v_head_1210_; lean_object* v_fst_1211_; lean_object* v_info_1212_; lean_object* v_tail_1213_; lean_object* v_collectKinds_1214_; lean_object* v___x_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_head_1210_ = lean_ctor_get(v_as_x27_1208_, 0);
v_fst_1211_ = lean_ctor_get(v_head_1210_, 0);
v_info_1212_ = lean_ctor_get(v_fst_1211_, 0);
v_tail_1213_ = lean_ctor_get(v_as_x27_1208_, 1);
v_collectKinds_1214_ = lean_ctor_get(v_info_1212_, 1);
v___x_1215_ = lean_box(v___x_1207_);
lean_inc(v_a_1206_);
lean_inc_ref(v_tactics_1205_);
v___f_1216_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1216_, 0, v_tactics_1205_);
lean_closure_set(v___f_1216_, 1, v_a_1206_);
lean_closure_set(v___f_1216_, 2, v___x_1215_);
v___x_1217_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1214_);
v___x_1218_ = lean_apply_1(v_collectKinds_1214_, v___x_1217_);
v___x_1219_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1218_, v_b_1209_, v___f_1216_);
lean_dec_ref(v___x_1218_);
v_as_x27_1208_ = v_tail_1213_;
v_b_1209_ = v___x_1219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1221_, lean_object* v_a_1222_, lean_object* v___x_1223_, lean_object* v_as_x27_1224_, lean_object* v_b_1225_){
_start:
{
uint8_t v___x_4416__boxed_1226_; lean_object* v_res_1227_; 
v___x_4416__boxed_1226_ = lean_unbox(v___x_1223_);
v_res_1227_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1221_, v_a_1222_, v___x_4416__boxed_1226_, v_as_x27_1224_, v_b_1225_);
lean_dec(v_as_x27_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1231_, lean_object* v_init_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v_k_1234_; lean_object* v_v_1235_; lean_object* v_l_1236_; lean_object* v_r_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_k_1234_ = lean_ctor_get(v_x_1233_, 1);
lean_inc(v_k_1234_);
v_v_1235_ = lean_ctor_get(v_x_1233_, 2);
lean_inc(v_v_1235_);
v_l_1236_ = lean_ctor_get(v_x_1233_, 3);
lean_inc(v_l_1236_);
v_r_1237_ = lean_ctor_get(v_x_1233_, 4);
lean_inc(v_r_1237_);
lean_dec_ref_known(v_x_1233_, 5);
lean_inc_ref(v_tactics_1231_);
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1231_, v_init_1232_, v_l_1236_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
v___x_1240_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1241_ = lean_name_eq(v_k_1234_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_dec_ref(v___x_1238_);
lean_inc_ref(v_tactics_1231_);
v___x_1242_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1231_, v_k_1234_, v___x_1241_, v_v_1235_, v_a_1239_);
lean_dec(v_v_1235_);
v_init_1232_ = v___x_1242_;
v_x_1233_ = v_r_1237_;
goto _start;
}
else
{
lean_object* v_a_1244_; 
lean_dec(v_a_1239_);
lean_dec(v_v_1235_);
lean_dec(v_k_1234_);
v_a_1244_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1238_);
v_init_1232_ = v_a_1244_;
v_x_1233_ = v_r_1237_;
goto _start;
}
}
else
{
lean_object* v___x_1246_; 
lean_dec_ref(v_tactics_1231_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_init_1232_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1247_, lean_object* v_table_1248_, lean_object* v_firsts_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v_a_1251_; 
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1247_, v_firsts_1249_, v_table_1248_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1250_);
return v_a_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1256_, v_x_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec_ref(v_x_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1261_, lean_object* v_k_1262_, lean_object* v_t_1263_, lean_object* v_hl_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1261_, v_k_1262_, v_t_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_map_1268_, lean_object* v_init_1269_, lean_object* v_f_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1268_, v_init_1269_, v_f_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_map_1274_, lean_object* v_init_1275_, lean_object* v_f_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1272_, v_00_u03b2_1273_, v_map_1274_, v_init_1275_, v_f_1276_);
lean_dec_ref(v_map_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1278_, lean_object* v_a_1279_, uint8_t v___x_1280_, lean_object* v_as_1281_, lean_object* v_as_x27_1282_, lean_object* v_b_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1278_, v_a_1279_, v___x_1280_, v_as_x27_1282_, v_b_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1286_, lean_object* v_a_1287_, lean_object* v___x_1288_, lean_object* v_as_1289_, lean_object* v_as_x27_1290_, lean_object* v_b_1291_, lean_object* v_a_1292_){
_start:
{
uint8_t v___x_4499__boxed_1293_; lean_object* v_res_1294_; 
v___x_4499__boxed_1293_ = lean_unbox(v___x_1288_);
v_res_1294_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1286_, v_a_1287_, v___x_4499__boxed_1293_, v_as_1289_, v_as_x27_1290_, v_b_1291_, v_a_1292_);
lean_dec(v_as_x27_1290_);
lean_dec(v_as_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1295_, lean_object* v_x_1296_, size_t v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1296_, v_x_1297_, v_x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
size_t v_x_4508__boxed_1304_; uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_x_4508__boxed_1304_ = lean_unbox_usize(v_x_1302_);
lean_dec(v_x_1302_);
v_res_1305_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1300_, v_x_1301_, v_x_4508__boxed_1304_, v_x_1303_);
lean_dec(v_x_1303_);
lean_dec_ref(v_x_1301_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1307_, lean_object* v_f_1308_, lean_object* v_init_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1308_, v_map_1307_, v_init_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1311_, lean_object* v_00_u03c3_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_map_1314_, lean_object* v_f_1315_, lean_object* v_init_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1315_, v_map_1314_, v_init_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1318_, lean_object* v_keys_1319_, lean_object* v_vals_1320_, lean_object* v_heq_1321_, lean_object* v_i_1322_, lean_object* v_k_1323_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1319_, v_i_1322_, v_k_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1325_, lean_object* v_keys_1326_, lean_object* v_vals_1327_, lean_object* v_heq_1328_, lean_object* v_i_1329_, lean_object* v_k_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1325_, v_keys_1326_, v_vals_1327_, v_heq_1328_, v_i_1329_, v_k_1330_);
lean_dec(v_k_1330_);
lean_dec_ref(v_vals_1327_);
lean_dec_ref(v_keys_1326_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1333_, lean_object* v_00_u03c3_1334_, lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_f_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1337_, v_x_1338_, v_x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_00_u03c3_1343_, lean_object* v_00_u03c3_1344_, lean_object* v_f_1345_, lean_object* v_as_1346_, size_t v_i_1347_, size_t v_stop_1348_, lean_object* v_b_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1345_, v_as_1346_, v_i_1347_, v_stop_1348_, v_b_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_00_u03c3_1353_, lean_object* v_00_u03c3_1354_, lean_object* v_f_1355_, lean_object* v_as_1356_, lean_object* v_i_1357_, lean_object* v_stop_1358_, lean_object* v_b_1359_){
_start:
{
size_t v_i_boxed_1360_; size_t v_stop_boxed_1361_; lean_object* v_res_1362_; 
v_i_boxed_1360_ = lean_unbox_usize(v_i_1357_);
lean_dec(v_i_1357_);
v_stop_boxed_1361_ = lean_unbox_usize(v_stop_1358_);
lean_dec(v_stop_1358_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1351_, v_00_u03b2_1352_, v_00_u03c3_1353_, v_00_u03c3_1354_, v_f_1355_, v_as_1356_, v_i_boxed_1360_, v_stop_boxed_1361_, v_b_1359_);
lean_dec_ref(v_as_1356_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1363_, lean_object* v_00_u03c3_1364_, lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_f_1367_, lean_object* v_keys_1368_, lean_object* v_vals_1369_, lean_object* v_heq_1370_, lean_object* v_i_1371_, lean_object* v_acc_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1367_, v_keys_1368_, v_vals_1369_, v_i_1371_, v_acc_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1374_, lean_object* v_00_u03c3_1375_, lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_f_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_heq_1381_, lean_object* v_i_1382_, lean_object* v_acc_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1374_, v_00_u03c3_1375_, v_00_u03b1_1376_, v_00_u03b2_1377_, v_f_1378_, v_keys_1379_, v_vals_1380_, v_heq_1381_, v_i_1382_, v_acc_1383_);
lean_dec_ref(v_vals_1380_);
lean_dec_ref(v_keys_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1385_, lean_object* v_x2_1386_){
_start:
{
lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v___x_1389_; 
v_fst_1387_ = lean_ctor_get(v_x2_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v_x2_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec_ref(v_x2_1386_);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1387_, v_snd_1388_, v_x1_1385_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1409_, lean_object* v_x1_1410_, lean_object* v_x2_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_x2_1411_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1415_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1415_ == 0)
{
lean_dec_ref(v_x2_1411_);
lean_dec_ref(v___f_1409_);
return v_x1_1410_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_le(v___x_1413_, v___x_1413_);
if (v___x_1416_ == 0)
{
if (v___x_1415_ == 0)
{
lean_dec_ref(v_x2_1411_);
lean_dec_ref(v___f_1409_);
return v_x1_1410_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1413_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1414_, v___f_1409_, v_x2_1411_, v___x_1417_, v___x_1418_, v_x1_1410_);
return v___x_1419_;
}
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1413_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1414_, v___f_1409_, v_x2_1411_, v___x_1420_, v___x_1421_, v_x1_1410_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v_toPure_1431_, lean_object* v___f_1432_, lean_object* v_env_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v_ext_1435_; lean_object* v_toEnvExtension_1436_; lean_object* v_asyncMode_1437_; lean_object* v___x_1438_; lean_object* v_categories_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1434_ = l_Lean_Parser_parserExtension;
v_ext_1435_ = lean_ctor_get(v___x_1434_, 1);
v_toEnvExtension_1436_ = lean_ctor_get(v_ext_1435_, 0);
v_asyncMode_1437_ = lean_ctor_get(v_toEnvExtension_1436_, 2);
lean_inc_ref(v_env_1433_);
v___x_1438_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1426_, v___x_1434_, v_env_1433_, v_asyncMode_1437_);
v_categories_1439_ = lean_ctor_get(v___x_1438_, 2);
lean_inc_ref(v_categories_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1441_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1427_, v___x_1428_, v_categories_1439_, v___x_1440_);
lean_dec_ref(v_categories_1439_);
if (lean_obj_tag(v___x_1441_) == 1)
{
lean_object* v_val_1442_; lean_object* v___y_1444_; lean_object* v___x_1451_; lean_object* v_toEnvExtension_1452_; lean_object* v_exportEntriesFn_1453_; lean_object* v_asyncMode_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_importedEntries_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_exported_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_val_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1451_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1452_ = lean_ctor_get(v___x_1451_, 0);
v_exportEntriesFn_1453_ = lean_ctor_get(v___x_1451_, 4);
v_asyncMode_1454_ = lean_ctor_get(v_toEnvExtension_1452_, 2);
v___x_1455_ = lean_box(0);
lean_inc_ref_n(v_env_1433_, 2);
v___x_1456_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1429_, v_toEnvExtension_1452_, v_env_1433_, v_asyncMode_1454_, v___x_1455_);
v_importedEntries_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_importedEntries_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1430_, v___x_1451_, v_env_1433_, v_asyncMode_1454_, v___x_1455_);
lean_inc_ref(v_exportEntriesFn_1453_);
v___x_1459_ = lean_apply_2(v_exportEntriesFn_1453_, v_env_1433_, v___x_1458_);
v_exported_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_exported_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = lean_box(1);
v___x_1462_ = lean_array_push(v_importedEntries_1457_, v_exported_1460_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_array_get_size(v___x_1462_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1466_ = lean_nat_dec_lt(v___x_1463_, v___x_1464_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1462_);
lean_dec_ref(v___f_1432_);
v___y_1444_ = v___x_1461_;
goto v___jp_1443_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_le(v___x_1464_, v___x_1464_);
if (v___x_1467_ == 0)
{
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1462_);
lean_dec_ref(v___f_1432_);
v___y_1444_ = v___x_1461_;
goto v___jp_1443_;
}
else
{
size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1464_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1465_, v___f_1432_, v___x_1462_, v___x_1468_, v___x_1469_, v___x_1461_);
v___y_1444_ = v___x_1470_;
goto v___jp_1443_;
}
}
else
{
size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1464_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1465_, v___f_1432_, v___x_1462_, v___x_1471_, v___x_1472_, v___x_1461_);
v___y_1444_ = v___x_1473_;
goto v___jp_1443_;
}
}
v___jp_1443_:
{
lean_object* v_tables_1445_; lean_object* v_leadingTable_1446_; lean_object* v_trailingTable_1447_; lean_object* v_firstTokens_1448_; lean_object* v_firstTokens_1449_; lean_object* v___x_1450_; 
v_tables_1445_ = lean_ctor_get(v_val_1442_, 2);
v_leadingTable_1446_ = lean_ctor_get(v_tables_1445_, 0);
v_trailingTable_1447_ = lean_ctor_get(v_tables_1445_, 2);
lean_inc(v_trailingTable_1447_);
lean_inc(v_leadingTable_1446_);
lean_inc(v_val_1442_);
v_firstTokens_1448_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1442_, v_leadingTable_1446_, v___y_1444_);
v_firstTokens_1449_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1442_, v_trailingTable_1447_, v_firstTokens_1448_);
v___x_1450_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_firstTokens_1449_);
return v___x_1450_;
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v___x_1441_);
lean_dec_ref(v_env_1433_);
lean_dec_ref(v___f_1432_);
lean_dec(v___x_1430_);
v___x_1474_ = lean_box(1);
v___x_1475_ = lean_apply_2(v_toPure_1431_, lean_box(0), v___x_1474_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v_toPure_1481_, lean_object* v___f_1482_, lean_object* v_env_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1476_, v___x_1477_, v___x_1478_, v___x_1479_, v___x_1480_, v_toPure_1481_, v___f_1482_, v_env_1483_);
lean_dec_ref(v___x_1479_);
lean_dec_ref(v___x_1476_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(1);
v___x_1489_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1492_, lean_object* v_inst_1493_){
_start:
{
lean_object* v_toApplicative_1494_; lean_object* v_toBind_1495_; lean_object* v_getEnv_1496_; lean_object* v_toPure_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; 
v_toApplicative_1494_ = lean_ctor_get(v_inst_1492_, 0);
lean_inc_ref(v_toApplicative_1494_);
v_toBind_1495_ = lean_ctor_get(v_inst_1492_, 1);
lean_inc(v_toBind_1495_);
lean_dec_ref(v_inst_1492_);
v_getEnv_1496_ = lean_ctor_get(v_inst_1493_, 0);
lean_inc(v_getEnv_1496_);
lean_dec_ref(v_inst_1493_);
v_toPure_1497_ = lean_ctor_get(v_toApplicative_1494_, 1);
lean_inc(v_toPure_1497_);
lean_dec_ref(v_toApplicative_1494_);
v___f_1498_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1499_ = lean_box(1);
v___x_1500_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1501_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1503_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1504_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1504_, 0, v___x_1503_);
lean_closure_set(v___f_1504_, 1, v___x_1501_);
lean_closure_set(v___f_1504_, 2, v___x_1502_);
lean_closure_set(v___f_1504_, 3, v___x_1500_);
lean_closure_set(v___f_1504_, 4, v___x_1499_);
lean_closure_set(v___f_1504_, 5, v_toPure_1497_);
lean_closure_set(v___f_1504_, 6, v___f_1498_);
v___x_1505_ = lean_apply_4(v_toBind_1495_, lean_box(0), lean_box(0), v_getEnv_1496_, v___f_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1507_, v_inst_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_box(1);
v___x_1514_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1515_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1514_);
lean_ctor_set(v___x_1516_, 2, v___x_1513_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_1518_, lean_object* v___y_1519_, lean_object* v_toPure_1520_, lean_object* v_firsts_1521_, lean_object* v_____do__lift_1522_){
_start:
{
lean_object* v___y_1524_; lean_object* v_val_1535_; 
if (lean_obj_tag(v_____do__lift_1522_) == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3));
lean_inc(v_n_1518_);
v___x_1538_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1537_, v_firsts_1521_, v_n_1518_);
if (lean_obj_tag(v___x_1538_) == 0)
{
uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = 1;
lean_inc(v_n_1518_);
v___x_1540_ = l_Lean_Name_toString(v_n_1518_, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___y_1524_ = v___x_1541_;
goto v___jp_1523_;
}
else
{
lean_object* v_val_1542_; 
v_val_1542_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v___x_1538_, 1);
v_val_1535_ = v_val_1542_;
goto v___jp_1534_;
}
}
else
{
lean_object* v_val_1543_; 
lean_dec(v_firsts_1521_);
v_val_1543_ = lean_ctor_get(v_____do__lift_1522_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v_____do__lift_1522_, 1);
v_val_1535_ = v_val_1543_;
goto v___jp_1534_;
}
v___jp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1525_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1526_ = l_Lean_Expr_const___override(v_n_1518_, v___y_1519_);
v___x_1527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1528_ = lean_box(0);
v___x_1529_ = 0;
v___x_1530_ = l_Lean_MessageData_withExprHover(v___y_1524_, v___x_1526_, v___x_1527_, v___x_1528_, v___x_1528_, v___x_1528_, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1525_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1525_);
v___x_1533_ = lean_apply_2(v_toPure_1520_, lean_box(0), v___x_1532_);
return v___x_1533_;
}
v___jp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_val_1535_);
v___y_1524_ = v___x_1536_;
goto v___jp_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_1544_, lean_object* v_toPure_1545_, lean_object* v_firsts_1546_, lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_toBind_1549_, lean_object* v___x_1550_, lean_object* v___x_1551_, lean_object* v___f_1552_, lean_object* v_env_1553_){
_start:
{
lean_object* v___y_1555_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Lean_Environment_constants(v_env_1553_);
lean_inc(v_n_1544_);
v___x_1560_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1550_, v___x_1551_, v___x_1559_, v_n_1544_);
lean_dec_ref(v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; 
lean_dec_ref(v___f_1552_);
v___x_1561_ = lean_box(0);
v___y_1555_ = v___x_1561_;
goto v___jp_1554_;
}
else
{
lean_object* v_val_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_val_1562_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_val_1562_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1563_ = l_Lean_ConstantInfo_levelParams(v_val_1562_);
lean_dec(v_val_1562_);
v___x_1564_ = lean_box(0);
v___x_1565_ = l_List_mapTR_loop___redArg(v___f_1552_, v___x_1563_, v___x_1564_);
v___y_1555_ = v___x_1565_;
goto v___jp_1554_;
}
v___jp_1554_:
{
lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_inc(v_n_1544_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1556_, 0, v_n_1544_);
lean_closure_set(v___f_1556_, 1, v___y_1555_);
lean_closure_set(v___f_1556_, 2, v_toPure_1545_);
lean_closure_set(v___f_1556_, 3, v_firsts_1546_);
v___x_1557_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1547_, v_inst_1548_, v_n_1544_);
v___x_1558_ = lean_apply_4(v_toBind_1549_, lean_box(0), lean_box(0), v___x_1557_, v___f_1556_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_firsts_1569_, lean_object* v_n_1570_){
_start:
{
lean_object* v_toApplicative_1571_; lean_object* v_toBind_1572_; lean_object* v_getEnv_1573_; lean_object* v_toPure_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; 
v_toApplicative_1571_ = lean_ctor_get(v_inst_1567_, 0);
v_toBind_1572_ = lean_ctor_get(v_inst_1567_, 1);
lean_inc_n(v_toBind_1572_, 2);
v_getEnv_1573_ = lean_ctor_get(v_inst_1568_, 0);
lean_inc(v_getEnv_1573_);
v_toPure_1574_ = lean_ctor_get(v_toApplicative_1571_, 1);
lean_inc(v_toPure_1574_);
v___f_1575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1577_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1578_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1578_, 0, v_n_1570_);
lean_closure_set(v___f_1578_, 1, v_toPure_1574_);
lean_closure_set(v___f_1578_, 2, v_firsts_1569_);
lean_closure_set(v___f_1578_, 3, v_inst_1567_);
lean_closure_set(v___f_1578_, 4, v_inst_1568_);
lean_closure_set(v___f_1578_, 5, v_toBind_1572_);
lean_closure_set(v___f_1578_, 6, v___x_1576_);
lean_closure_set(v___f_1578_, 7, v___x_1577_);
lean_closure_set(v___f_1578_, 8, v___f_1575_);
v___x_1579_ = lean_apply_4(v_toBind_1572_, lean_box(0), lean_box(0), v_getEnv_1573_, v___f_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_firsts_1583_, lean_object* v_n_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1581_, v_inst_1582_, v_firsts_1583_, v_n_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1590_);
lean_dec_ref(v_s_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1592_, lean_object* v_x1_1593_, lean_object* v_x2_1594_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = l_Lean_Name_toString(v_x1_1593_, v___x_1592_);
v___x_1596_ = l_Lean_Name_toString(v_x2_1594_, v___x_1592_);
v___x_1597_ = lean_string_dec_lt(v___x_1595_, v___x_1596_);
lean_dec_ref(v___x_1596_);
lean_dec_ref(v___x_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1598_, lean_object* v_x1_1599_, lean_object* v_x2_1600_){
_start:
{
uint8_t v___x_17024__boxed_1601_; uint8_t v_res_1602_; lean_object* v_r_1603_; 
v___x_17024__boxed_1601_ = lean_unbox(v___x_1598_);
v_res_1602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_17024__boxed_1601_, v_x1_1599_, v_x2_1600_);
v_r_1603_ = lean_box(v_res_1602_);
return v_r_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1604_, lean_object* v_pivot_1605_, lean_object* v_as_1606_, lean_object* v_i_1607_, lean_object* v_k_1608_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_nat_dec_lt(v_k_1608_, v_hi_1604_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v_k_1608_);
lean_dec(v_pivot_1605_);
v___x_1610_ = lean_array_fswap(v_as_1606_, v_i_1607_, v_hi_1604_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_i_1607_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1612_ = lean_array_fget_borrowed(v_as_1606_, v_k_1608_);
lean_inc(v___x_1612_);
v___x_1613_ = l_Lean_Name_toString(v___x_1612_, v___x_1609_);
lean_inc(v_pivot_1605_);
v___x_1614_ = l_Lean_Name_toString(v_pivot_1605_, v___x_1609_);
v___x_1615_ = lean_string_dec_lt(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
lean_dec_ref(v___x_1613_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_nat_add(v_k_1608_, v___x_1616_);
lean_dec(v_k_1608_);
v_k_1608_ = v___x_1617_;
goto _start;
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1619_ = lean_array_fswap(v_as_1606_, v_i_1607_, v_k_1608_);
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_nat_add(v_i_1607_, v___x_1620_);
lean_dec(v_i_1607_);
v___x_1622_ = lean_nat_add(v_k_1608_, v___x_1620_);
lean_dec(v_k_1608_);
v_as_1606_ = v___x_1619_;
v_i_1607_ = v___x_1621_;
v_k_1608_ = v___x_1622_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1624_, lean_object* v_pivot_1625_, lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_k_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1624_, v_pivot_1625_, v_as_1626_, v_i_1627_, v_k_1628_);
lean_dec(v_hi_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1630_, lean_object* v_as_1631_, lean_object* v_lo_1632_, lean_object* v_hi_1633_){
_start:
{
lean_object* v___y_1635_; uint8_t v___x_1645_; 
v___x_1645_ = lean_nat_dec_lt(v_lo_1632_, v_hi_1633_);
if (v___x_1645_ == 0)
{
lean_dec(v_lo_1632_);
return v_as_1631_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v_mid_1648_; lean_object* v___y_1650_; lean_object* v___y_1656_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1646_ = lean_nat_add(v_lo_1632_, v_hi_1633_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v_mid_1648_ = lean_nat_shiftr(v___x_1646_, v___x_1647_);
lean_dec(v___x_1646_);
v___x_1661_ = lean_array_fget_borrowed(v_as_1631_, v_mid_1648_);
v___x_1662_ = lean_array_fget_borrowed(v_as_1631_, v_lo_1632_);
lean_inc(v___x_1662_);
lean_inc(v___x_1661_);
v___x_1663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1645_, v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
v___y_1656_ = v_as_1631_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_array_fswap(v_as_1631_, v_lo_1632_, v_mid_1648_);
v___y_1656_ = v___x_1664_;
goto v___jp_1655_;
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_array_fget_borrowed(v___y_1650_, v_mid_1648_);
v___x_1652_ = lean_array_fget_borrowed(v___y_1650_, v_hi_1633_);
lean_inc(v___x_1652_);
lean_inc(v___x_1651_);
v___x_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1645_, v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_dec(v_mid_1648_);
v___y_1635_ = v___y_1650_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_fswap(v___y_1650_, v_mid_1648_, v_hi_1633_);
lean_dec(v_mid_1648_);
v___y_1635_ = v___x_1654_;
goto v___jp_1634_;
}
}
v___jp_1655_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = lean_array_fget_borrowed(v___y_1656_, v_hi_1633_);
v___x_1658_ = lean_array_fget_borrowed(v___y_1656_, v_lo_1632_);
lean_inc(v___x_1658_);
lean_inc(v___x_1657_);
v___x_1659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1645_, v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
v___y_1650_ = v___y_1656_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_array_fswap(v___y_1656_, v_lo_1632_, v_hi_1633_);
v___y_1650_ = v___x_1660_;
goto v___jp_1649_;
}
}
}
v___jp_1634_:
{
lean_object* v_pivot_1636_; lean_object* v___x_1637_; lean_object* v_fst_1638_; lean_object* v_snd_1639_; uint8_t v___x_1640_; 
v_pivot_1636_ = lean_array_fget(v___y_1635_, v_hi_1633_);
lean_inc_n(v_lo_1632_, 2);
v___x_1637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1633_, v_pivot_1636_, v___y_1635_, v_lo_1632_, v_lo_1632_);
v_fst_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_fst_1638_);
v_snd_1639_ = lean_ctor_get(v___x_1637_, 1);
lean_inc(v_snd_1639_);
lean_dec_ref(v___x_1637_);
v___x_1640_ = lean_nat_dec_le(v_hi_1633_, v_fst_1638_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1630_, v_snd_1639_, v_lo_1632_, v_fst_1638_);
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_add(v_fst_1638_, v___x_1642_);
lean_dec(v_fst_1638_);
v_as_1631_ = v___x_1641_;
v_lo_1632_ = v___x_1643_;
goto _start;
}
else
{
lean_dec(v_fst_1638_);
lean_dec(v_lo_1632_);
return v_snd_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1665_, lean_object* v_as_1666_, lean_object* v_lo_1667_, lean_object* v_hi_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1665_, v_as_1666_, v_lo_1667_, v_hi_1668_);
lean_dec(v_hi_1668_);
lean_dec(v_n_1665_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1670_, lean_object* v_x_1671_){
_start:
{
if (lean_obj_tag(v_x_1671_) == 0)
{
lean_object* v_k_1672_; lean_object* v_l_1673_; lean_object* v_r_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_k_1672_ = lean_ctor_get(v_x_1671_, 1);
lean_inc(v_k_1672_);
v_l_1673_ = lean_ctor_get(v_x_1671_, 3);
lean_inc(v_l_1673_);
v_r_1674_ = lean_ctor_get(v_x_1671_, 4);
lean_inc(v_r_1674_);
lean_dec_ref_known(v_x_1671_, 5);
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1670_, v_l_1673_);
v___x_1676_ = lean_array_push(v___x_1675_, v_k_1672_);
v_init_1670_ = v___x_1676_;
v_x_1671_ = v_r_1674_;
goto _start;
}
else
{
return v_init_1670_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
if (lean_obj_tag(v_a_1678_) == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = l_List_reverse___redArg(v_a_1679_);
return v___x_1680_;
}
else
{
lean_object* v_head_1681_; lean_object* v_tail_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v_head_1681_ = lean_ctor_get(v_a_1678_, 0);
v_tail_1682_ = lean_ctor_get(v_a_1678_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1678_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1684_ = v_a_1678_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_tail_1682_);
lean_inc(v_head_1681_);
lean_dec(v_a_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_Level_param___override(v_head_1681_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v_a_1679_);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_a_1679_);
v___x_1688_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
v_a_1678_ = v_tail_1682_;
v_a_1679_ = v___x_1688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1692_, lean_object* v_x2_1693_){
_start:
{
lean_object* v_fst_1694_; lean_object* v_fst_1695_; uint8_t v___x_1696_; 
v_fst_1694_ = lean_ctor_get(v_x1_1692_, 0);
v_fst_1695_ = lean_ctor_get(v_x2_1693_, 0);
v___x_1696_ = l_Lean_Name_quickLt(v_fst_1694_, v_fst_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1697_, lean_object* v_x2_1698_){
_start:
{
uint8_t v_res_1699_; lean_object* v_r_1700_; 
v_res_1699_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1697_, v_x2_1698_);
lean_dec_ref(v_x2_1698_);
lean_dec_ref(v_x1_1697_);
v_r_1700_ = lean_box(v_res_1699_);
return v_r_1700_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1701_, lean_object* v_k_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_m_1707_; lean_object* v_a_1708_; uint8_t v___x_1709_; 
v___x_1705_ = lean_nat_add(v_x_1703_, v_x_1704_);
v___x_1706_ = lean_unsigned_to_nat(1u);
v_m_1707_ = lean_nat_shiftr(v___x_1705_, v___x_1706_);
lean_dec(v___x_1705_);
v_a_1708_ = lean_array_fget_borrowed(v_as_1701_, v_m_1707_);
v___x_1709_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1708_, v_k_1702_);
if (v___x_1709_ == 0)
{
uint8_t v___x_1710_; 
lean_dec(v_x_1704_);
v___x_1710_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1702_, v_a_1708_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v_m_1707_);
lean_dec(v_x_1703_);
lean_inc(v_a_1708_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_a_1708_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_nat_dec_eq(v_m_1707_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = lean_nat_sub(v_m_1707_, v___x_1706_);
lean_dec(v_m_1707_);
v___x_1715_ = lean_nat_dec_lt(v___x_1714_, v_x_1703_);
if (v___x_1715_ == 0)
{
v_x_1704_ = v___x_1714_;
goto _start;
}
else
{
lean_object* v___x_1717_; 
lean_dec(v___x_1714_);
lean_dec(v_x_1703_);
v___x_1717_ = lean_box(0);
return v___x_1717_;
}
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_m_1707_);
lean_dec(v_x_1703_);
v___x_1718_ = lean_box(0);
return v___x_1718_;
}
}
}
else
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
lean_dec(v_x_1703_);
v___x_1719_ = lean_nat_add(v_m_1707_, v___x_1706_);
lean_dec(v_m_1707_);
v___x_1720_ = lean_nat_dec_le(v___x_1719_, v_x_1704_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; 
lean_dec(v___x_1719_);
lean_dec(v_x_1704_);
v___x_1721_ = lean_box(0);
return v___x_1721_;
}
else
{
v_x_1703_ = v___x_1719_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1723_, lean_object* v_k_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1723_, v_k_1724_, v_x_1725_, v_x_1726_);
lean_dec_ref(v_k_1724_);
lean_dec_ref(v_as_1723_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v_env_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1732_ = lean_st_ref_get(v___y_1730_);
v_env_1736_ = lean_ctor_get(v___x_1732_, 0);
lean_inc_ref(v_env_1736_);
lean_dec(v___x_1732_);
v___x_1737_ = lean_box(1);
v___x_1738_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1736_, v_tac_1729_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v___x_1739_; lean_object* v_toEnvExtension_1740_; lean_object* v_asyncMode_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1739_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1740_ = lean_ctor_get(v___x_1739_, 0);
v_asyncMode_1741_ = lean_ctor_get(v_toEnvExtension_1740_, 2);
v___x_1742_ = lean_box(0);
v___x_1743_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1737_, v___x_1739_, v_env_1736_, v_asyncMode_1741_, v___x_1742_);
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1743_, v_tac_1729_);
lean_dec(v_tac_1729_);
lean_dec(v___x_1743_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
else
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1774_; 
v_val_1746_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1748_ = v___x_1738_;
v_isShared_1749_ = v_isSharedCheck_1774_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v___x_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1774_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1750_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1751_ = 0;
v___x_1752_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1737_, v___x_1750_, v_env_1736_, v_val_1746_, v___x_1751_);
lean_dec(v_val_1746_);
lean_dec_ref(v_env_1736_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_array_get_size(v___x_1752_);
v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v___x_1752_);
lean_del_object(v___x_1748_);
lean_dec(v_tac_1729_);
goto v___jp_1733_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_sub(v___x_1754_, v___x_1756_);
v___x_1758_ = lean_nat_dec_le(v___x_1753_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec(v___x_1757_);
lean_dec_ref(v___x_1752_);
lean_del_object(v___x_1748_);
lean_dec(v_tac_1729_);
goto v___jp_1733_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_tac_1729_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1752_, v___x_1760_, v___x_1753_, v___x_1757_);
lean_dec_ref_known(v___x_1760_, 2);
lean_dec_ref(v___x_1752_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_del_object(v___x_1748_);
goto v___jp_1733_;
}
else
{
lean_object* v_val_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1773_; 
v_val_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1773_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_val_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1773_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_snd_1766_; lean_object* v___x_1768_; 
v_snd_1766_ = lean_ctor_get(v_val_1762_, 1);
lean_inc(v_snd_1766_);
lean_dec(v_val_1762_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v_snd_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_snd_1766_);
v___x_1768_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1768_);
v___x_1770_ = v___x_1748_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
}
}
v___jp_1733_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1775_, v___y_1776_);
lean_dec(v___y_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1779_, lean_object* v_k_1780_){
_start:
{
if (lean_obj_tag(v_t_1779_) == 0)
{
lean_object* v_k_1781_; lean_object* v_v_1782_; lean_object* v_l_1783_; lean_object* v_r_1784_; uint8_t v___x_1785_; 
v_k_1781_ = lean_ctor_get(v_t_1779_, 1);
v_v_1782_ = lean_ctor_get(v_t_1779_, 2);
v_l_1783_ = lean_ctor_get(v_t_1779_, 3);
v_r_1784_ = lean_ctor_get(v_t_1779_, 4);
v___x_1785_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1780_, v_k_1781_);
switch(v___x_1785_)
{
case 0:
{
v_t_1779_ = v_l_1783_;
goto _start;
}
case 1:
{
lean_object* v___x_1787_; 
lean_inc(v_v_1782_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_v_1782_);
return v___x_1787_;
}
default: 
{
v_t_1779_ = v_r_1784_;
goto _start;
}
}
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_box(0);
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1790_, lean_object* v_k_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1790_, v_k_1791_);
lean_dec(v_k_1791_);
lean_dec(v_t_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_1793_, lean_object* v_x_1794_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_box(0);
return v___x_1795_;
}
else
{
lean_object* v_key_1796_; lean_object* v_value_1797_; lean_object* v_tail_1798_; uint8_t v___x_1799_; 
v_key_1796_ = lean_ctor_get(v_x_1794_, 0);
v_value_1797_ = lean_ctor_get(v_x_1794_, 1);
v_tail_1798_ = lean_ctor_get(v_x_1794_, 2);
v___x_1799_ = lean_name_eq(v_key_1796_, v_a_1793_);
if (v___x_1799_ == 0)
{
v_x_1794_ = v_tail_1798_;
goto _start;
}
else
{
lean_object* v___x_1801_; 
lean_inc(v_value_1797_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_value_1797_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_1802_, lean_object* v_x_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1802_, v_x_1803_);
lean_dec(v_x_1803_);
lean_dec(v_a_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_buckets_1807_; lean_object* v___x_1808_; uint64_t v___y_1810_; 
v_buckets_1807_ = lean_ctor_get(v_m_1805_, 1);
v___x_1808_ = lean_array_get_size(v_buckets_1807_);
if (lean_obj_tag(v_a_1806_) == 0)
{
uint64_t v___x_1824_; 
v___x_1824_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1810_ = v___x_1824_;
goto v___jp_1809_;
}
else
{
uint64_t v_hash_1825_; 
v_hash_1825_ = lean_ctor_get_uint64(v_a_1806_, sizeof(void*)*2);
v___y_1810_ = v_hash_1825_;
goto v___jp_1809_;
}
v___jp_1809_:
{
uint64_t v___x_1811_; uint64_t v___x_1812_; uint64_t v_fold_1813_; uint64_t v___x_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; size_t v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1811_ = 32ULL;
v___x_1812_ = lean_uint64_shift_right(v___y_1810_, v___x_1811_);
v_fold_1813_ = lean_uint64_xor(v___y_1810_, v___x_1812_);
v___x_1814_ = 16ULL;
v___x_1815_ = lean_uint64_shift_right(v_fold_1813_, v___x_1814_);
v___x_1816_ = lean_uint64_xor(v_fold_1813_, v___x_1815_);
v___x_1817_ = lean_uint64_to_usize(v___x_1816_);
v___x_1818_ = lean_usize_of_nat(v___x_1808_);
v___x_1819_ = ((size_t)1ULL);
v___x_1820_ = lean_usize_sub(v___x_1818_, v___x_1819_);
v___x_1821_ = lean_usize_land(v___x_1817_, v___x_1820_);
v___x_1822_ = lean_array_uget_borrowed(v_buckets_1807_, v___x_1821_);
v___x_1823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1806_, v___x_1822_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_m_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1829_, lean_object* v_vals_1830_, lean_object* v_i_1831_, lean_object* v_k_1832_){
_start:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_array_get_size(v_keys_1829_);
v___x_1834_ = lean_nat_dec_lt(v_i_1831_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v_i_1831_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
else
{
lean_object* v_k_x27_1836_; uint8_t v___x_1837_; 
v_k_x27_1836_ = lean_array_fget_borrowed(v_keys_1829_, v_i_1831_);
v___x_1837_ = lean_name_eq(v_k_1832_, v_k_x27_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_add(v_i_1831_, v___x_1838_);
lean_dec(v_i_1831_);
v_i_1831_ = v___x_1839_;
goto _start;
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_array_fget_borrowed(v_vals_1830_, v_i_1831_);
lean_dec(v_i_1831_);
lean_inc(v___x_1841_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1843_, lean_object* v_vals_1844_, lean_object* v_i_1845_, lean_object* v_k_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1843_, v_vals_1844_, v_i_1845_, v_k_1846_);
lean_dec(v_k_1846_);
lean_dec_ref(v_vals_1844_);
lean_dec_ref(v_keys_1843_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1848_, size_t v_x_1849_, lean_object* v_x_1850_){
_start:
{
if (lean_obj_tag(v_x_1848_) == 0)
{
lean_object* v_es_1851_; lean_object* v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v_j_1856_; lean_object* v___x_1857_; 
v_es_1851_ = lean_ctor_get(v_x_1848_, 0);
v___x_1852_ = lean_box(2);
v___x_1853_ = ((size_t)5ULL);
v___x_1854_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1855_ = lean_usize_land(v_x_1849_, v___x_1854_);
v_j_1856_ = lean_usize_to_nat(v___x_1855_);
v___x_1857_ = lean_array_get_borrowed(v___x_1852_, v_es_1851_, v_j_1856_);
lean_dec(v_j_1856_);
switch(lean_obj_tag(v___x_1857_))
{
case 0:
{
lean_object* v_key_1858_; lean_object* v_val_1859_; uint8_t v___x_1860_; 
v_key_1858_ = lean_ctor_get(v___x_1857_, 0);
v_val_1859_ = lean_ctor_get(v___x_1857_, 1);
v___x_1860_ = lean_name_eq(v_x_1850_, v_key_1858_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_box(0);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
lean_inc(v_val_1859_);
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_val_1859_);
return v___x_1862_;
}
}
case 1:
{
lean_object* v_node_1863_; size_t v___x_1864_; 
v_node_1863_ = lean_ctor_get(v___x_1857_, 0);
v___x_1864_ = lean_usize_shift_right(v_x_1849_, v___x_1853_);
v_x_1848_ = v_node_1863_;
v_x_1849_ = v___x_1864_;
goto _start;
}
default: 
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_box(0);
return v___x_1866_;
}
}
}
else
{
lean_object* v_ks_1867_; lean_object* v_vs_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_ks_1867_ = lean_ctor_get(v_x_1848_, 0);
v_vs_1868_ = lean_ctor_get(v_x_1848_, 1);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1867_, v_vs_1868_, v___x_1869_, v_x_1850_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
size_t v_x_17406__boxed_1874_; lean_object* v_res_1875_; 
v_x_17406__boxed_1874_ = lean_unbox_usize(v_x_1872_);
lean_dec(v_x_1872_);
v_res_1875_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1871_, v_x_17406__boxed_1874_, v_x_1873_);
lean_dec(v_x_1873_);
lean_dec_ref(v_x_1871_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
uint64_t v___y_1879_; 
if (lean_obj_tag(v_x_1877_) == 0)
{
uint64_t v___x_1882_; 
v___x_1882_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1879_ = v___x_1882_;
goto v___jp_1878_;
}
else
{
uint64_t v_hash_1883_; 
v_hash_1883_ = lean_ctor_get_uint64(v_x_1877_, sizeof(void*)*2);
v___y_1879_ = v_hash_1883_;
goto v___jp_1878_;
}
v___jp_1878_:
{
size_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_uint64_to_usize(v___y_1879_);
v___x_1881_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1876_, v___x_1880_, v_x_1877_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1884_, v_x_1885_);
lean_dec(v_x_1885_);
lean_dec_ref(v_x_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
uint8_t v_stage_u2081_1889_; 
v_stage_u2081_1889_ = lean_ctor_get_uint8(v_x_1887_, sizeof(void*)*2);
if (v_stage_u2081_1889_ == 0)
{
lean_object* v_map_u2081_1890_; lean_object* v_map_u2082_1891_; lean_object* v___x_1892_; 
v_map_u2081_1890_ = lean_ctor_get(v_x_1887_, 0);
v_map_u2082_1891_ = lean_ctor_get(v_x_1887_, 1);
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1890_, v_x_1888_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1891_, v_x_1888_);
return v___x_1893_;
}
else
{
return v___x_1892_;
}
}
else
{
lean_object* v_map_u2081_1894_; lean_object* v___x_1895_; 
v_map_u2081_1894_ = lean_ctor_get(v_x_1887_, 0);
v___x_1895_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1894_, v_x_1888_);
return v___x_1895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1896_, v_x_1897_);
lean_dec(v_x_1897_);
lean_dec_ref(v_x_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1899_, lean_object* v_n_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1919_; lean_object* v_val_1920_; lean_object* v___x_1922_; lean_object* v___y_1924_; lean_object* v_env_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1922_ = lean_st_ref_get(v___y_1902_);
v_env_1939_ = lean_ctor_get(v___x_1922_, 0);
lean_inc_ref(v_env_1939_);
lean_dec(v___x_1922_);
v___x_1940_ = l_Lean_Environment_constants(v_env_1939_);
v___x_1941_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_1940_, v_n_1900_);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_box(0);
v___y_1924_ = v___x_1942_;
goto v___jp_1923_;
}
else
{
lean_object* v_val_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_val_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1944_ = l_Lean_ConstantInfo_levelParams(v_val_1943_);
lean_dec(v_val_1943_);
v___x_1945_ = lean_box(0);
v___x_1946_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_1944_, v___x_1945_);
v___y_1924_ = v___x_1946_;
goto v___jp_1923_;
}
v___jp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1907_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1908_ = l_Lean_Expr_const___override(v_n_1900_, v___y_1905_);
v___x_1909_ = lean_unsigned_to_nat(32u);
v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
lean_dec_ref(v___x_1910_);
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1912_ = lean_box(0);
v___x_1913_ = 0;
v___x_1914_ = l_Lean_MessageData_withExprHover(v___y_1906_, v___x_1908_, v___x_1911_, v___x_1912_, v___x_1912_, v___x_1912_, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1907_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1907_);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
v___jp_1918_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_val_1920_);
v___y_1905_ = v___y_1919_;
v___y_1906_ = v___x_1921_;
goto v___jp_1904_;
}
v___jp_1923_:
{
lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1938_; 
lean_inc(v_n_1900_);
v___x_1925_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1900_, v___y_1902_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1938_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1938_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
if (lean_obj_tag(v_a_1926_) == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1899_, v_n_1900_);
if (lean_obj_tag(v___x_1930_) == 0)
{
uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1931_ = 1;
lean_inc(v_n_1900_);
v___x_1932_ = l_Lean_Name_toString(v_n_1900_, v___x_1931_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 3);
lean_ctor_set(v___x_1928_, 0, v___x_1932_);
v___x_1934_ = v___x_1928_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
v___y_1905_ = v___y_1924_;
v___y_1906_ = v___x_1934_;
goto v___jp_1904_;
}
}
else
{
lean_object* v_val_1936_; 
lean_del_object(v___x_1928_);
v_val_1936_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v___x_1930_, 1);
v___y_1919_ = v___y_1924_;
v_val_1920_ = v_val_1936_;
goto v___jp_1918_;
}
}
else
{
lean_object* v_val_1937_; 
lean_del_object(v___x_1928_);
v_val_1937_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_a_1926_, 1);
v___y_1919_ = v___y_1924_;
v_val_1920_ = v_val_1937_;
goto v___jp_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_1947_, lean_object* v_n_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_1947_, v_n_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_firsts_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
if (lean_obj_tag(v_x_1954_) == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = l_List_reverse___redArg(v_x_1955_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
return v___x_1960_;
}
else
{
lean_object* v_head_1961_; lean_object* v_tail_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1980_; 
v_head_1961_ = lean_ctor_get(v_x_1954_, 0);
v_tail_1962_ = lean_ctor_get(v_x_1954_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_x_1954_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1964_ = v_x_1954_;
v_isShared_1965_ = v_isSharedCheck_1980_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_tail_1962_);
lean_inc(v_head_1961_);
lean_dec(v_x_1954_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1980_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; 
v___x_1966_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_1953_, v_head_1961_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 1, v_x_1955_);
lean_ctor_set(v___x_1964_, 0, v_a_1967_);
v___x_1969_ = v___x_1964_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1967_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_x_1955_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
v_x_1954_ = v_tail_1962_;
v_x_1955_ = v___x_1969_;
goto _start;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1964_);
lean_dec(v_tail_1962_);
lean_dec(v_x_1955_);
v_a_1972_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1966_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1966_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_1981_, v_x_1982_, v_x_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v_a_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_1988_, lean_object* v___x_1989_, lean_object* v___x_1990_, lean_object* v_a_1991_, lean_object* v_b_1992_){
_start:
{
lean_object* v_it_1994_; lean_object* v_startInclusive_1995_; lean_object* v_endExclusive_1996_; 
if (lean_obj_tag(v_a_1991_) == 0)
{
lean_object* v_currPos_2001_; lean_object* v_searcher_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2028_; 
v_currPos_2001_ = lean_ctor_get(v_a_1991_, 0);
v_searcher_2002_ = lean_ctor_get(v_a_1991_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_a_1991_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2004_ = v_a_1991_;
v_isShared_2005_ = v_isSharedCheck_2028_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_searcher_2002_);
lean_inc(v_currPos_2001_);
lean_dec(v_a_1991_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2028_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_startInclusive_2006_; lean_object* v_endExclusive_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_startInclusive_2006_ = lean_ctor_get(v___x_1989_, 1);
v_endExclusive_2007_ = lean_ctor_get(v___x_1989_, 2);
v___x_2008_ = lean_nat_sub(v_endExclusive_2007_, v_startInclusive_2006_);
v___x_2009_ = lean_nat_dec_eq(v_searcher_2002_, v___x_2008_);
lean_dec(v___x_2008_);
if (v___x_2009_ == 0)
{
uint32_t v___x_2010_; uint32_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = 10;
v___x_2011_ = lean_string_utf8_get_fast(v_val_1988_, v_searcher_2002_);
v___x_2012_ = lean_uint32_dec_eq(v___x_2011_, v___x_2010_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_string_utf8_next_fast(v_val_1988_, v_searcher_2002_);
lean_dec(v_searcher_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2013_);
v___x_2015_ = v___x_2004_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_currPos_2001_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
v_a_1991_ = v___x_2015_;
goto _start;
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_slice_2021_; lean_object* v_nextIt_2023_; 
v___x_2018_ = lean_string_utf8_next_fast(v_val_1988_, v_searcher_2002_);
v___x_2019_ = lean_nat_sub(v___x_2018_, v_searcher_2002_);
v___x_2020_ = lean_nat_add(v_searcher_2002_, v___x_2019_);
lean_dec(v___x_2019_);
v_slice_2021_ = l_String_Slice_subslice_x21(v___x_1989_, v_currPos_2001_, v_searcher_2002_);
lean_inc(v___x_2020_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2020_);
lean_ctor_set(v___x_2004_, 0, v___x_2020_);
v_nextIt_2023_ = v___x_2004_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2020_);
v_nextIt_2023_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v_startInclusive_2024_; lean_object* v_endExclusive_2025_; 
v_startInclusive_2024_ = lean_ctor_get(v_slice_2021_, 0);
lean_inc(v_startInclusive_2024_);
v_endExclusive_2025_ = lean_ctor_get(v_slice_2021_, 1);
lean_inc(v_endExclusive_2025_);
lean_dec_ref(v_slice_2021_);
v_it_1994_ = v_nextIt_2023_;
v_startInclusive_1995_ = v_startInclusive_2024_;
v_endExclusive_1996_ = v_endExclusive_2025_;
goto v___jp_1993_;
}
}
}
else
{
lean_object* v___x_2027_; 
lean_del_object(v___x_2004_);
lean_dec(v_searcher_2002_);
v___x_2027_ = lean_box(1);
lean_inc(v___x_1990_);
v_it_1994_ = v___x_2027_;
v_startInclusive_1995_ = v_currPos_2001_;
v_endExclusive_1996_ = v___x_1990_;
goto v___jp_1993_;
}
}
}
else
{
lean_dec(v___x_1990_);
return v_b_1992_;
}
v___jp_1993_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = lean_string_utf8_extract(v_val_1988_, v_startInclusive_1995_, v_endExclusive_1996_);
lean_dec(v_endExclusive_1996_);
lean_dec(v_startInclusive_1995_);
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
v___x_1999_ = lean_array_push(v_b_1992_, v___x_1998_);
v_a_1991_ = v_it_1994_;
v_b_1992_ = v___x_1999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2029_, lean_object* v___x_2030_, lean_object* v___x_2031_, lean_object* v_a_2032_, lean_object* v_b_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2029_, v___x_2030_, v___x_2031_, v_a_2032_, v_b_2033_);
lean_dec_ref(v___x_2030_);
lean_dec_ref(v_val_2029_);
return v_res_2034_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2045_ = l_Lean_stringToMessageData(v___x_2044_);
return v___x_2045_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2050_ = l_Lean_MessageData_ofFormat(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
if (lean_obj_tag(v_x_2053_) == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = l_List_reverse___redArg(v_x_2054_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
else
{
lean_object* v_head_2060_; lean_object* v_tail_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2158_; 
v_head_2060_ = lean_ctor_get(v_x_2053_, 0);
v_tail_2061_ = lean_ctor_get(v_x_2053_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_2053_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2063_ = v_x_2053_;
v_isShared_2064_ = v_isSharedCheck_2158_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_tail_2061_);
lean_inc(v_head_2060_);
lean_dec(v_x_2053_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2158_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v_snd_2078_; lean_object* v_fst_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2157_; 
v_snd_2078_ = lean_ctor_get(v_head_2060_, 1);
v_fst_2079_ = lean_ctor_get(v_head_2060_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_head_2060_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2081_ = v_head_2060_;
v_isShared_2082_ = v_isSharedCheck_2157_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2078_);
lean_inc(v_fst_2079_);
lean_dec(v_head_2060_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2157_;
goto v_resetjp_2080_;
}
v___jp_2065_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___y_2068_);
lean_ctor_set(v___x_2070_, 1, v___y_2069_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___y_2066_);
v___x_2072_ = l_Lean_MessageData_nestD(v___x_2071_);
lean_inc_ref(v___y_2067_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___y_2067_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v_x_2054_);
lean_ctor_set(v___x_2063_, 0, v___x_2073_);
v___x_2075_ = v___x_2063_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_x_2054_);
v___x_2075_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
v_x_2053_ = v_tail_2061_;
v_x_2054_ = v___x_2075_;
goto _start;
}
}
v_resetjp_2080_:
{
lean_object* v_fst_2083_; lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2156_; 
v_fst_2083_ = lean_ctor_get(v_snd_2078_, 0);
v_snd_2084_ = lean_ctor_get(v_snd_2078_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_snd_2078_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2086_ = v_snd_2078_;
v_isShared_2087_ = v_isSharedCheck_2156_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_inc(v_fst_2083_);
lean_dec(v_snd_2078_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2156_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v_a_2111_; lean_object* v___y_2127_; lean_object* v___x_2136_; 
v___x_2136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2052_, v_fst_2079_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_MessageData_nil;
v_a_2111_ = v___x_2137_;
goto v___jp_2110_;
}
else
{
lean_object* v_val_2138_; 
v_val_2138_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_val_2138_);
lean_dec_ref_known(v___x_2136_, 1);
if (lean_obj_tag(v_val_2138_) == 0)
{
lean_object* v_size_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_size_2139_ = lean_ctor_get(v_val_2138_, 0);
v___x_2140_ = lean_mk_empty_array_with_capacity(v_size_2139_);
v___x_2141_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2140_, v_val_2138_);
v___x_2142_ = lean_array_get_size(v___x_2141_);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_nat_dec_eq(v___x_2142_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___y_2152_; uint8_t v___x_2154_; 
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = lean_nat_sub(v___x_2142_, v___x_2149_);
v___x_2154_ = lean_nat_dec_le(v___x_2147_, v___x_2150_);
if (v___x_2154_ == 0)
{
lean_inc(v___x_2150_);
v___y_2152_ = v___x_2150_;
goto v___jp_2151_;
}
else
{
v___y_2152_ = v___x_2147_;
goto v___jp_2151_;
}
v___jp_2151_:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_nat_dec_le(v___y_2152_, v___x_2150_);
if (v___x_2153_ == 0)
{
lean_dec(v___x_2150_);
lean_inc(v___y_2152_);
v___y_2144_ = v___y_2152_;
v___y_2145_ = v___y_2152_;
goto v___jp_2143_;
}
else
{
v___y_2144_ = v___y_2152_;
v___y_2145_ = v___x_2150_;
goto v___jp_2143_;
}
}
}
else
{
v___y_2127_ = v___x_2141_;
goto v___jp_2126_;
}
v___jp_2143_:
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2142_, v___x_2141_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
v___y_2127_ = v___x_2146_;
goto v___jp_2126_;
}
}
else
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_MessageData_nil;
v_a_2111_ = v___x_2155_;
goto v___jp_2110_;
}
}
v___jp_2088_:
{
lean_object* v___x_2094_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set_tag(v___x_2086_, 7);
lean_ctor_set(v___x_2086_, 1, v___y_2092_);
lean_ctor_set(v___x_2086_, 0, v___y_2090_);
v___x_2094_ = v___x_2086_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___y_2090_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___y_2092_);
v___x_2094_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
if (lean_obj_tag(v_snd_2084_) == 0)
{
lean_object* v___x_2095_; 
lean_del_object(v___x_2081_);
v___x_2095_ = l_Lean_MessageData_nil;
v___y_2066_ = v___y_2089_;
v___y_2067_ = v___y_2091_;
v___y_2068_ = v___x_2094_;
v___y_2069_ = v___x_2095_;
goto v___jp_2065_;
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
v_val_2096_ = lean_ctor_get(v_snd_2084_, 0);
lean_inc_n(v_val_2096_, 2);
lean_dec_ref_known(v_snd_2084_, 1);
v___x_2097_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = lean_string_utf8_byte_size(v_val_2096_);
v___x_2100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2100_, 0, v_val_2096_);
lean_ctor_set(v___x_2100_, 1, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v___x_2099_);
v___x_2101_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2100_);
v___x_2102_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2103_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2096_, v___x_2100_, v___x_2099_, v___x_2101_, v___x_2102_);
lean_dec_ref_known(v___x_2100_, 3);
lean_dec(v_val_2096_);
v___x_2104_ = lean_array_to_list(v___x_2103_);
v___x_2105_ = l_Lean_MessageData_joinSep(v___x_2104_, v___x_2097_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 7);
lean_ctor_set(v___x_2081_, 1, v___x_2105_);
lean_ctor_set(v___x_2081_, 0, v___x_2097_);
v___x_2107_ = v___x_2081_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v___y_2066_ = v___y_2089_;
v___y_2067_ = v___y_2091_;
v___y_2068_ = v___x_2094_;
v___y_2069_ = v___x_2107_;
goto v___jp_2065_;
}
}
}
}
v___jp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2112_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2113_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2079_);
v___x_2114_ = l_Lean_MessageData_ofName(v_fst_2079_);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2113_);
v___x_2117_ = 1;
v___x_2118_ = l_Lean_Name_toString(v_fst_2079_, v___x_2117_);
v___x_2119_ = lean_string_dec_eq(v___x_2118_, v_fst_2083_);
lean_dec_ref(v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2120_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2121_ = l_Lean_stringToMessageData(v_fst_2083_);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___y_2089_ = v_a_2111_;
v___y_2090_ = v___x_2116_;
v___y_2091_ = v___x_2112_;
v___y_2092_ = v___x_2124_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2125_; 
lean_dec(v_fst_2083_);
v___x_2125_ = l_Lean_MessageData_nil;
v___y_2089_ = v_a_2111_;
v___y_2090_ = v___x_2116_;
v___y_2091_ = v___x_2112_;
v___y_2092_ = v___x_2125_;
goto v___jp_2088_;
}
}
v___jp_2126_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_array_to_list(v___y_2127_);
v___x_2129_ = lean_box(0);
v___x_2130_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2051_, v___x_2128_, v___x_2129_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2133_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2134_ = l_Lean_MessageData_joinSep(v_a_2131_, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v_a_2111_ = v___x_2135_;
goto v___jp_2110_;
}
else
{
lean_del_object(v___x_2086_);
lean_dec(v_snd_2084_);
lean_dec(v_fst_2083_);
lean_del_object(v___x_2081_);
lean_dec(v_fst_2079_);
lean_del_object(v___x_2063_);
lean_dec(v_tail_2061_);
lean_dec(v_x_2054_);
return v___x_2130_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2159_, v_a_2160_, v_x_2161_, v_x_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_a_2160_);
lean_dec(v_a_2159_);
return v_res_2166_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v___y_2168_, uint8_t v_suppressElabErrors_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2170_) == 1)
{
lean_object* v_pre_2171_; 
v_pre_2171_ = lean_ctor_get(v_x_2170_, 0);
if (lean_obj_tag(v_pre_2171_) == 0)
{
lean_object* v_str_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_str_2172_ = lean_ctor_get(v_x_2170_, 1);
v___x_2173_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2174_ = lean_string_dec_eq(v_str_2172_, v___x_2173_);
if (v___x_2174_ == 0)
{
return v___y_2168_;
}
else
{
return v_suppressElabErrors_2169_;
}
}
else
{
return v___y_2168_;
}
}
else
{
return v___y_2168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v___y_2175_, lean_object* v_suppressElabErrors_2176_, lean_object* v_x_2177_){
_start:
{
uint8_t v___y_18028__boxed_2178_; uint8_t v_suppressElabErrors_boxed_2179_; uint8_t v_res_2180_; lean_object* v_r_2181_; 
v___y_18028__boxed_2178_ = lean_unbox(v___y_2175_);
v_suppressElabErrors_boxed_2179_ = lean_unbox(v_suppressElabErrors_2176_);
v_res_2180_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v___y_18028__boxed_2178_, v_suppressElabErrors_boxed_2179_, v_x_2177_);
lean_dec(v_x_2177_);
v_r_2181_ = lean_box(v_res_2180_);
return v_r_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2182_, lean_object* v_msgData_2183_, uint8_t v_severity_2184_, uint8_t v_isSilent_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; uint8_t v___y_2253_; uint8_t v___y_2254_; uint8_t v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; uint8_t v___y_2281_; uint8_t v___y_2282_; lean_object* v___y_2283_; uint8_t v___y_2284_; lean_object* v___y_2285_; uint8_t v___y_2289_; uint8_t v___y_2290_; uint8_t v___y_2291_; uint8_t v___x_2306_; uint8_t v___y_2308_; uint8_t v___y_2309_; uint8_t v___y_2310_; uint8_t v___y_2312_; uint8_t v___x_2324_; 
v___x_2306_ = 2;
v___x_2324_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2184_, v___x_2306_);
if (v___x_2324_ == 0)
{
v___y_2312_ = v___x_2324_;
goto v___jp_2311_;
}
else
{
uint8_t v___x_2325_; 
lean_inc_ref(v_msgData_2183_);
v___x_2325_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2183_);
v___y_2312_ = v___x_2325_;
goto v___jp_2311_;
}
v___jp_2189_:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Elab_Command_getScope___redArg(v___y_2197_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = l_Lean_Elab_Command_getScope___redArg(v___y_2197_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2235_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2235_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2235_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v_currNamespace_2206_; lean_object* v_openDecls_2207_; lean_object* v_env_2208_; lean_object* v_messages_2209_; lean_object* v_scopes_2210_; lean_object* v_usedQuotCtxts_2211_; lean_object* v_nextMacroScope_2212_; lean_object* v_maxRecDepth_2213_; lean_object* v_ngen_2214_; lean_object* v_auxDeclNGen_2215_; lean_object* v_infoState_2216_; lean_object* v_traceState_2217_; lean_object* v_snapshotTasks_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2234_; 
v___x_2205_ = lean_st_ref_take(v___y_2197_);
v_currNamespace_2206_ = lean_ctor_get(v_a_2199_, 2);
lean_inc(v_currNamespace_2206_);
lean_dec(v_a_2199_);
v_openDecls_2207_ = lean_ctor_get(v_a_2201_, 3);
lean_inc(v_openDecls_2207_);
lean_dec(v_a_2201_);
v_env_2208_ = lean_ctor_get(v___x_2205_, 0);
v_messages_2209_ = lean_ctor_get(v___x_2205_, 1);
v_scopes_2210_ = lean_ctor_get(v___x_2205_, 2);
v_usedQuotCtxts_2211_ = lean_ctor_get(v___x_2205_, 3);
v_nextMacroScope_2212_ = lean_ctor_get(v___x_2205_, 4);
v_maxRecDepth_2213_ = lean_ctor_get(v___x_2205_, 5);
v_ngen_2214_ = lean_ctor_get(v___x_2205_, 6);
v_auxDeclNGen_2215_ = lean_ctor_get(v___x_2205_, 7);
v_infoState_2216_ = lean_ctor_get(v___x_2205_, 8);
v_traceState_2217_ = lean_ctor_get(v___x_2205_, 9);
v_snapshotTasks_2218_ = lean_ctor_get(v___x_2205_, 10);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2220_ = v___x_2205_;
v_isShared_2221_ = v_isSharedCheck_2234_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_snapshotTasks_2218_);
lean_inc(v_traceState_2217_);
lean_inc(v_infoState_2216_);
lean_inc(v_auxDeclNGen_2215_);
lean_inc(v_ngen_2214_);
lean_inc(v_maxRecDepth_2213_);
lean_inc(v_nextMacroScope_2212_);
lean_inc(v_usedQuotCtxts_2211_);
lean_inc(v_scopes_2210_);
lean_inc(v_messages_2209_);
lean_inc(v_env_2208_);
lean_dec(v___x_2205_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2234_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_currNamespace_2206_);
lean_ctor_set(v___x_2222_, 1, v_openDecls_2207_);
v___x_2223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___y_2194_);
lean_inc_ref(v___y_2195_);
lean_inc_ref(v___y_2196_);
v___x_2224_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2224_, 0, v___y_2196_);
lean_ctor_set(v___x_2224_, 1, v___y_2192_);
lean_ctor_set(v___x_2224_, 2, v___y_2193_);
lean_ctor_set(v___x_2224_, 3, v___y_2195_);
lean_ctor_set(v___x_2224_, 4, v___x_2223_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*5, v___y_2191_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*5 + 1, v___y_2190_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*5 + 2, v_isSilent_2185_);
v___x_2225_ = l_Lean_MessageLog_add(v___x_2224_, v_messages_2209_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2225_);
v___x_2227_ = v___x_2220_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_env_2208_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_scopes_2210_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_usedQuotCtxts_2211_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v_nextMacroScope_2212_);
lean_ctor_set(v_reuseFailAlloc_2233_, 5, v_maxRecDepth_2213_);
lean_ctor_set(v_reuseFailAlloc_2233_, 6, v_ngen_2214_);
lean_ctor_set(v_reuseFailAlloc_2233_, 7, v_auxDeclNGen_2215_);
lean_ctor_set(v_reuseFailAlloc_2233_, 8, v_infoState_2216_);
lean_ctor_set(v_reuseFailAlloc_2233_, 9, v_traceState_2217_);
lean_ctor_set(v_reuseFailAlloc_2233_, 10, v_snapshotTasks_2218_);
v___x_2227_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = lean_st_ref_set(v___y_2197_, v___x_2227_);
v___x_2229_ = lean_box(0);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2229_);
v___x_2231_ = v___x_2203_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2199_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
v_a_2236_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2200_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2200_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
v_a_2244_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2198_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2198_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
v___jp_2252_:
{
lean_object* v_fileName_2258_; lean_object* v_fileMap_2259_; uint8_t v_suppressElabErrors_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2279_; 
v_fileName_2258_ = lean_ctor_get(v___y_2186_, 0);
v_fileMap_2259_ = lean_ctor_get(v___y_2186_, 1);
v_suppressElabErrors_2260_ = lean_ctor_get_uint8(v___y_2186_, sizeof(void*)*10);
v___x_2261_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2183_);
v___x_2262_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2261_, v___y_2187_);
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2279_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2279_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_inc_ref_n(v_fileMap_2259_, 2);
v___x_2267_ = l_Lean_FileMap_toPosition(v_fileMap_2259_, v___y_2256_);
lean_dec(v___y_2256_);
v___x_2268_ = l_Lean_FileMap_toPosition(v_fileMap_2259_, v___y_2257_);
lean_dec(v___y_2257_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2260_ == 0)
{
lean_del_object(v___x_2265_);
v___y_2190_ = v___y_2254_;
v___y_2191_ = v___y_2255_;
v___y_2192_ = v___x_2267_;
v___y_2193_ = v___x_2269_;
v___y_2194_ = v_a_2263_;
v___y_2195_ = v___x_2270_;
v___y_2196_ = v_fileName_2258_;
v___y_2197_ = v___y_2187_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; uint8_t v___x_2274_; 
v___x_2271_ = lean_box(v___y_2253_);
v___x_2272_ = lean_box(v_suppressElabErrors_2260_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2273_, 0, v___x_2271_);
lean_closure_set(v___f_2273_, 1, v___x_2272_);
lean_inc(v_a_2263_);
v___x_2274_ = l_Lean_MessageData_hasTag(v___f_2273_, v_a_2263_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_dec_ref_known(v___x_2269_, 1);
lean_dec_ref(v___x_2267_);
lean_dec(v_a_2263_);
v___x_2275_ = lean_box(0);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2275_);
v___x_2277_ = v___x_2265_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_del_object(v___x_2265_);
v___y_2190_ = v___y_2254_;
v___y_2191_ = v___y_2255_;
v___y_2192_ = v___x_2267_;
v___y_2193_ = v___x_2269_;
v___y_2194_ = v_a_2263_;
v___y_2195_ = v___x_2270_;
v___y_2196_ = v_fileName_2258_;
v___y_2197_ = v___y_2187_;
goto v___jp_2189_;
}
}
}
}
v___jp_2280_:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Syntax_getTailPos_x3f(v___y_2283_, v___y_2284_);
lean_dec(v___y_2283_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_inc(v___y_2285_);
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
v___y_2255_ = v___y_2284_;
v___y_2256_ = v___y_2285_;
v___y_2257_ = v___y_2285_;
goto v___jp_2252_;
}
else
{
lean_object* v_val_2287_; 
v_val_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
v___y_2255_ = v___y_2284_;
v___y_2256_ = v___y_2285_;
v___y_2257_ = v_val_2287_;
goto v___jp_2252_;
}
}
v___jp_2288_:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Elab_Command_getRef___redArg(v___y_2186_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v_ref_2294_; lean_object* v___x_2295_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v_ref_2294_ = l_Lean_replaceRef(v_ref_2182_, v_a_2293_);
lean_dec(v_a_2293_);
v___x_2295_ = l_Lean_Syntax_getPos_x3f(v_ref_2294_, v___y_2290_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_unsigned_to_nat(0u);
v___y_2281_ = v___y_2289_;
v___y_2282_ = v___y_2291_;
v___y_2283_ = v_ref_2294_;
v___y_2284_ = v___y_2290_;
v___y_2285_ = v___x_2296_;
goto v___jp_2280_;
}
else
{
lean_object* v_val_2297_; 
v_val_2297_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2297_);
lean_dec_ref_known(v___x_2295_, 1);
v___y_2281_ = v___y_2289_;
v___y_2282_ = v___y_2291_;
v___y_2283_ = v_ref_2294_;
v___y_2284_ = v___y_2290_;
v___y_2285_ = v_val_2297_;
goto v___jp_2280_;
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_msgData_2183_);
v_a_2298_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2292_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2292_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
v___jp_2307_:
{
if (v___y_2310_ == 0)
{
v___y_2289_ = v___y_2308_;
v___y_2290_ = v___y_2309_;
v___y_2291_ = v_severity_2184_;
goto v___jp_2288_;
}
else
{
v___y_2289_ = v___y_2308_;
v___y_2290_ = v___y_2309_;
v___y_2291_ = v___x_2306_;
goto v___jp_2288_;
}
}
v___jp_2311_:
{
if (v___y_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v_scopes_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_opts_2317_; uint8_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2313_ = lean_st_ref_get(v___y_2187_);
v_scopes_2314_ = lean_ctor_get(v___x_2313_, 2);
lean_inc(v_scopes_2314_);
lean_dec(v___x_2313_);
v___x_2315_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2316_ = l_List_head_x21___redArg(v___x_2315_, v_scopes_2314_);
lean_dec(v_scopes_2314_);
v_opts_2317_ = lean_ctor_get(v___x_2316_, 1);
lean_inc_ref(v_opts_2317_);
lean_dec(v___x_2316_);
v___x_2318_ = 1;
v___x_2319_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2184_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_dec_ref(v_opts_2317_);
v___y_2308_ = v___y_2312_;
v___y_2309_ = v___y_2312_;
v___y_2310_ = v___x_2319_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = l_Lean_warningAsError;
v___x_2321_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2317_, v___x_2320_);
lean_dec_ref(v_opts_2317_);
v___y_2308_ = v___y_2312_;
v___y_2309_ = v___y_2312_;
v___y_2310_ = v___x_2321_;
goto v___jp_2307_;
}
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_msgData_2183_);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2326_, lean_object* v_msgData_2327_, lean_object* v_severity_2328_, lean_object* v_isSilent_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v_severity_boxed_2333_; uint8_t v_isSilent_boxed_2334_; lean_object* v_res_2335_; 
v_severity_boxed_2333_ = lean_unbox(v_severity_2328_);
v_isSilent_boxed_2334_ = lean_unbox(v_isSilent_2329_);
v_res_2335_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2326_, v_msgData_2327_, v_severity_boxed_2333_, v_isSilent_boxed_2334_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v_ref_2326_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2336_, uint8_t v_severity_2337_, uint8_t v_isSilent_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Elab_Command_getRef___redArg(v___y_2339_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2343_, v_msgData_2336_, v_severity_2337_, v_isSilent_2338_, v___y_2339_, v___y_2340_);
lean_dec(v_a_2343_);
return v___x_2344_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_msgData_2336_);
v_a_2345_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2342_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2342_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2353_, lean_object* v_severity_2354_, lean_object* v_isSilent_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v_severity_boxed_2359_; uint8_t v_isSilent_boxed_2360_; lean_object* v_res_2361_; 
v_severity_boxed_2359_ = lean_unbox(v_severity_2354_);
v_isSilent_boxed_2360_ = lean_unbox(v_isSilent_2355_);
v_res_2361_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2353_, v_severity_boxed_2359_, v_isSilent_boxed_2360_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = 0;
v___x_2367_ = 0;
v___x_2368_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2362_, v___x_2366_, v___x_2367_, v___y_2363_, v___y_2364_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2374_, lean_object* v_x_2375_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 0)
{
lean_object* v_k_2377_; lean_object* v_v_2378_; lean_object* v_l_2379_; lean_object* v_r_2380_; lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v_a_2383_; lean_object* v___x_2384_; 
v_k_2377_ = lean_ctor_get(v_x_2375_, 1);
lean_inc(v_k_2377_);
v_v_2378_ = lean_ctor_get(v_x_2375_, 2);
lean_inc(v_v_2378_);
v_l_2379_ = lean_ctor_get(v_x_2375_, 3);
lean_inc(v_l_2379_);
v_r_2380_ = lean_ctor_get(v_x_2375_, 4);
lean_inc(v_r_2380_);
lean_dec_ref_known(v_x_2375_, 5);
v___x_2381_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2374_, v_l_2379_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref(v___x_2381_);
v_a_2383_ = lean_ctor_get(v_a_2382_, 0);
lean_inc(v_a_2383_);
lean_dec(v_a_2382_);
v___x_2384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2377_, v_v_2378_, v_a_2383_);
v_init_2374_ = v___x_2384_;
v_x_2375_ = v_r_2380_;
goto _start;
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_init_2374_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2388_, lean_object* v_x_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2388_, v_x_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2392_, lean_object* v_x1_2393_, lean_object* v_x2_2394_){
_start:
{
lean_object* v_fst_2395_; lean_object* v_fst_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_fst_2395_ = lean_ctor_get(v_x1_2393_, 0);
lean_inc(v_fst_2395_);
lean_dec_ref(v_x1_2393_);
v_fst_2396_ = lean_ctor_get(v_x2_2394_, 0);
lean_inc(v_fst_2396_);
lean_dec_ref(v_x2_2394_);
v___x_2397_ = l_Lean_Name_toString(v_fst_2395_, v___x_2392_);
v___x_2398_ = l_Lean_Name_toString(v_fst_2396_, v___x_2392_);
v___x_2399_ = lean_string_dec_lt(v___x_2397_, v___x_2398_);
lean_dec_ref(v___x_2398_);
lean_dec_ref(v___x_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2400_, lean_object* v_x1_2401_, lean_object* v_x2_2402_){
_start:
{
uint8_t v___x_18371__boxed_2403_; uint8_t v_res_2404_; lean_object* v_r_2405_; 
v___x_18371__boxed_2403_ = lean_unbox(v___x_2400_);
v_res_2404_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18371__boxed_2403_, v_x1_2401_, v_x2_2402_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2406_, lean_object* v_pivot_2407_, lean_object* v_as_2408_, lean_object* v_i_2409_, lean_object* v_k_2410_){
_start:
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_nat_dec_lt(v_k_2410_, v_hi_2406_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec(v_k_2410_);
lean_dec_ref(v_pivot_2407_);
v___x_2412_ = lean_array_fswap(v_as_2408_, v_i_2409_, v_hi_2406_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_i_2409_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; lean_object* v_fst_2415_; lean_object* v_fst_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2414_ = lean_array_fget_borrowed(v_as_2408_, v_k_2410_);
v_fst_2415_ = lean_ctor_get(v___x_2414_, 0);
v_fst_2416_ = lean_ctor_get(v_pivot_2407_, 0);
lean_inc(v_fst_2415_);
v___x_2417_ = l_Lean_Name_toString(v_fst_2415_, v___x_2411_);
lean_inc(v_fst_2416_);
v___x_2418_ = l_Lean_Name_toString(v_fst_2416_, v___x_2411_);
v___x_2419_ = lean_string_dec_lt(v___x_2417_, v___x_2418_);
lean_dec_ref(v___x_2418_);
lean_dec_ref(v___x_2417_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_nat_add(v_k_2410_, v___x_2420_);
lean_dec(v_k_2410_);
v_k_2410_ = v___x_2421_;
goto _start;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2423_ = lean_array_fswap(v_as_2408_, v_i_2409_, v_k_2410_);
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = lean_nat_add(v_i_2409_, v___x_2424_);
lean_dec(v_i_2409_);
v___x_2426_ = lean_nat_add(v_k_2410_, v___x_2424_);
lean_dec(v_k_2410_);
v_as_2408_ = v___x_2423_;
v_i_2409_ = v___x_2425_;
v_k_2410_ = v___x_2426_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2428_, lean_object* v_pivot_2429_, lean_object* v_as_2430_, lean_object* v_i_2431_, lean_object* v_k_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2428_, v_pivot_2429_, v_as_2430_, v_i_2431_, v_k_2432_);
lean_dec(v_hi_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2434_, lean_object* v_as_2435_, lean_object* v_lo_2436_, lean_object* v_hi_2437_){
_start:
{
lean_object* v___y_2439_; uint8_t v___x_2449_; 
v___x_2449_ = lean_nat_dec_lt(v_lo_2436_, v_hi_2437_);
if (v___x_2449_ == 0)
{
lean_dec(v_lo_2436_);
return v_as_2435_;
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_mid_2452_; lean_object* v___y_2454_; lean_object* v___y_2460_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2450_ = lean_nat_add(v_lo_2436_, v_hi_2437_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v_mid_2452_ = lean_nat_shiftr(v___x_2450_, v___x_2451_);
lean_dec(v___x_2450_);
v___x_2465_ = lean_array_fget_borrowed(v_as_2435_, v_mid_2452_);
v___x_2466_ = lean_array_fget_borrowed(v_as_2435_, v_lo_2436_);
lean_inc(v___x_2466_);
lean_inc(v___x_2465_);
v___x_2467_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2449_, v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
v___y_2460_ = v_as_2435_;
goto v___jp_2459_;
}
else
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_array_fswap(v_as_2435_, v_lo_2436_, v_mid_2452_);
v___y_2460_ = v___x_2468_;
goto v___jp_2459_;
}
v___jp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2455_ = lean_array_fget_borrowed(v___y_2454_, v_mid_2452_);
v___x_2456_ = lean_array_fget_borrowed(v___y_2454_, v_hi_2437_);
lean_inc(v___x_2456_);
lean_inc(v___x_2455_);
v___x_2457_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2449_, v___x_2455_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_dec(v_mid_2452_);
v___y_2439_ = v___y_2454_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_array_fswap(v___y_2454_, v_mid_2452_, v_hi_2437_);
lean_dec(v_mid_2452_);
v___y_2439_ = v___x_2458_;
goto v___jp_2438_;
}
}
v___jp_2459_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2461_ = lean_array_fget_borrowed(v___y_2460_, v_hi_2437_);
v___x_2462_ = lean_array_fget_borrowed(v___y_2460_, v_lo_2436_);
lean_inc(v___x_2462_);
lean_inc(v___x_2461_);
v___x_2463_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2449_, v___x_2461_, v___x_2462_);
if (v___x_2463_ == 0)
{
v___y_2454_ = v___y_2460_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_array_fswap(v___y_2460_, v_lo_2436_, v_hi_2437_);
v___y_2454_ = v___x_2464_;
goto v___jp_2453_;
}
}
}
v___jp_2438_:
{
lean_object* v_pivot_2440_; lean_object* v___x_2441_; lean_object* v_fst_2442_; lean_object* v_snd_2443_; uint8_t v___x_2444_; 
v_pivot_2440_ = lean_array_fget(v___y_2439_, v_hi_2437_);
lean_inc_n(v_lo_2436_, 2);
v___x_2441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2437_, v_pivot_2440_, v___y_2439_, v_lo_2436_, v_lo_2436_);
v_fst_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_fst_2442_);
v_snd_2443_ = lean_ctor_get(v___x_2441_, 1);
lean_inc(v_snd_2443_);
lean_dec_ref(v___x_2441_);
v___x_2444_ = lean_nat_dec_le(v_hi_2437_, v_fst_2442_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2434_, v_snd_2443_, v_lo_2436_, v_fst_2442_);
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = lean_nat_add(v_fst_2442_, v___x_2446_);
lean_dec(v_fst_2442_);
v_as_2435_ = v___x_2445_;
v_lo_2436_ = v___x_2447_;
goto _start;
}
else
{
lean_dec(v_fst_2442_);
lean_dec(v_lo_2436_);
return v_snd_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2469_, lean_object* v_as_2470_, lean_object* v_lo_2471_, lean_object* v_hi_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2469_, v_as_2470_, v_lo_2471_, v_hi_2472_);
lean_dec(v_hi_2472_);
lean_dec(v_n_2469_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2474_, lean_object* v_x_2475_){
_start:
{
if (lean_obj_tag(v_x_2475_) == 0)
{
lean_object* v_k_2476_; lean_object* v_v_2477_; lean_object* v_l_2478_; lean_object* v_r_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_k_2476_ = lean_ctor_get(v_x_2475_, 1);
v_v_2477_ = lean_ctor_get(v_x_2475_, 2);
v_l_2478_ = lean_ctor_get(v_x_2475_, 3);
v_r_2479_ = lean_ctor_get(v_x_2475_, 4);
v___x_2480_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2474_, v_l_2478_);
lean_inc(v_v_2477_);
lean_inc(v_k_2476_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_k_2476_);
lean_ctor_set(v___x_2481_, 1, v_v_2477_);
v___x_2482_ = lean_array_push(v___x_2480_, v___x_2481_);
v_init_2474_ = v___x_2482_;
v_x_2475_ = v_r_2479_;
goto _start;
}
else
{
return v_init_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2484_, lean_object* v_x_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2484_, v_x_2485_);
lean_dec(v_x_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2487_, size_t v_sz_2488_, size_t v_i_2489_, lean_object* v_b_2490_){
_start:
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_usize_dec_lt(v_i_2489_, v_sz_2488_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_b_2490_);
return v___x_2493_;
}
else
{
lean_object* v_a_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v_found_2497_; size_t v___x_2498_; size_t v___x_2499_; 
v_a_2494_ = lean_array_uget_borrowed(v_as_2487_, v_i_2489_);
v_fst_2495_ = lean_ctor_get(v_a_2494_, 0);
v_snd_2496_ = lean_ctor_get(v_a_2494_, 1);
lean_inc(v_snd_2496_);
lean_inc(v_fst_2495_);
v_found_2497_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2495_, v_snd_2496_, v_b_2490_);
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_add(v_i_2489_, v___x_2498_);
v_i_2489_ = v___x_2499_;
v_b_2490_ = v_found_2497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2501_, lean_object* v_sz_2502_, lean_object* v_i_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2502_);
lean_dec(v_sz_2502_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2503_);
lean_dec(v_i_2503_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2501_, v_sz_boxed_2506_, v_i_boxed_2507_, v_b_2504_);
lean_dec_ref(v_as_2501_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2509_, size_t v_sz_2510_, size_t v_i_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_usize_dec_lt(v_i_2511_, v_sz_2510_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_b_2512_);
return v___x_2517_;
}
else
{
lean_object* v_a_2518_; size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v_a_2518_ = lean_array_uget_borrowed(v_as_2509_, v_i_2511_);
v_sz_2519_ = lean_array_size(v_a_2518_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2518_, v_sz_2519_, v___x_2520_, v_b_2512_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; size_t v___x_2523_; size_t v___x_2524_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2523_ = ((size_t)1ULL);
v___x_2524_ = lean_usize_add(v_i_2511_, v___x_2523_);
v_i_2511_ = v___x_2524_;
v_b_2512_ = v_a_2522_;
goto _start;
}
else
{
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2526_, lean_object* v_sz_2527_, lean_object* v_i_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
size_t v_sz_boxed_2533_; size_t v_i_boxed_2534_; lean_object* v_res_2535_; 
v_sz_boxed_2533_ = lean_unbox_usize(v_sz_2527_);
lean_dec(v_sz_2527_);
v_i_boxed_2534_ = lean_unbox_usize(v_i_2528_);
lean_dec(v_i_2528_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2526_, v_sz_boxed_2533_, v_i_boxed_2534_, v_b_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_as_2526_);
return v_res_2535_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_box(1);
v___x_2537_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___y_2544_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___x_2559_; lean_object* v_env_2560_; lean_object* v___x_2561_; lean_object* v_toEnvExtension_2562_; lean_object* v_asyncMode_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_a_2569_; lean_object* v_a_2571_; lean_object* v_a_2594_; 
v___x_2559_ = lean_st_ref_get(v___y_2541_);
v_env_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_ref_n(v_env_2560_, 2);
lean_dec(v___x_2559_);
v___x_2561_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2562_ = lean_ctor_get(v___x_2561_, 0);
v_asyncMode_2563_ = lean_ctor_get(v_toEnvExtension_2562_, 2);
v___x_2564_ = lean_box(1);
v___x_2565_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2566_ = lean_box(0);
v___x_2567_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2564_, v___x_2561_, v_env_2560_, v_asyncMode_2563_, v___x_2566_);
v___x_2568_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2564_, v___x_2567_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref(v___x_2568_);
v_a_2594_ = lean_ctor_get(v_a_2569_, 0);
lean_inc(v_a_2594_);
lean_dec(v_a_2569_);
v_a_2571_ = v_a_2594_;
goto v___jp_2570_;
v___jp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_array_to_list(v___y_2544_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
v___jp_2547_:
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2549_, v___y_2548_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec(v___y_2549_);
v___y_2544_ = v___x_2552_;
goto v___jp_2543_;
}
v___jp_2553_:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_nat_dec_le(v___y_2557_, v___y_2556_);
if (v___x_2558_ == 0)
{
lean_dec(v___y_2556_);
lean_inc(v___y_2557_);
v___y_2548_ = v___y_2554_;
v___y_2549_ = v___y_2555_;
v___y_2550_ = v___y_2557_;
v___y_2551_ = v___y_2557_;
goto v___jp_2547_;
}
else
{
v___y_2548_ = v___y_2554_;
v___y_2549_ = v___y_2555_;
v___y_2550_ = v___y_2557_;
v___y_2551_ = v___y_2556_;
goto v___jp_2547_;
}
}
v___jp_2570_:
{
lean_object* v___x_2572_; lean_object* v_importedEntries_2573_; size_t v_sz_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2572_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2565_, v_toEnvExtension_2562_, v_env_2560_, v_asyncMode_2563_, v___x_2566_);
v_importedEntries_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc_ref(v_importedEntries_2573_);
lean_dec(v___x_2572_);
v_sz_2574_ = lean_array_size(v_importedEntries_2573_);
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2573_, v_sz_2574_, v___x_2575_, v_a_2571_, v___y_2540_, v___y_2541_);
lean_dec_ref(v_importedEntries_2573_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_arr_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2580_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2579_, v_a_2577_);
lean_dec(v_a_2577_);
v___x_2581_ = lean_array_get_size(v_arr_2580_);
v___x_2582_ = lean_nat_dec_eq(v___x_2581_, v___x_2578_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = lean_nat_sub(v___x_2581_, v___x_2583_);
v___x_2585_ = lean_nat_dec_le(v___x_2578_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_inc(v___x_2584_);
v___y_2554_ = v_arr_2580_;
v___y_2555_ = v___x_2581_;
v___y_2556_ = v___x_2584_;
v___y_2557_ = v___x_2584_;
goto v___jp_2553_;
}
else
{
v___y_2554_ = v_arr_2580_;
v___y_2555_ = v___x_2581_;
v___y_2556_ = v___x_2584_;
v___y_2557_ = v___x_2578_;
goto v___jp_2553_;
}
}
else
{
v___y_2544_ = v_arr_2580_;
goto v___jp_2543_;
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_a_2586_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2576_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2576_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2599_, lean_object* v_k_2600_, lean_object* v_fallback_2601_){
_start:
{
if (lean_obj_tag(v_t_2599_) == 0)
{
lean_object* v_k_2602_; lean_object* v_v_2603_; lean_object* v_l_2604_; lean_object* v_r_2605_; uint8_t v___x_2606_; 
v_k_2602_ = lean_ctor_get(v_t_2599_, 1);
v_v_2603_ = lean_ctor_get(v_t_2599_, 2);
v_l_2604_ = lean_ctor_get(v_t_2599_, 3);
v_r_2605_ = lean_ctor_get(v_t_2599_, 4);
v___x_2606_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2600_, v_k_2602_);
switch(v___x_2606_)
{
case 0:
{
v_t_2599_ = v_l_2604_;
goto _start;
}
case 1:
{
lean_inc(v_v_2603_);
return v_v_2603_;
}
default: 
{
v_t_2599_ = v_r_2605_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2601_);
return v_fallback_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2609_, lean_object* v_k_2610_, lean_object* v_fallback_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2609_, v_k_2610_, v_fallback_2611_);
lean_dec(v_fallback_2611_);
lean_dec(v_k_2610_);
lean_dec(v_t_2609_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2613_, size_t v_sz_2614_, size_t v_i_2615_, lean_object* v_b_2616_){
_start:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_usize_dec_lt(v_i_2615_, v_sz_2614_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_b_2616_);
return v___x_2619_;
}
else
{
lean_object* v_a_2620_; lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; size_t v___x_2627_; size_t v___x_2628_; 
v_a_2620_ = lean_array_uget_borrowed(v_as_2613_, v_i_2615_);
v_fst_2621_ = lean_ctor_get(v_a_2620_, 0);
v_snd_2622_ = lean_ctor_get(v_a_2620_, 1);
v___x_2623_ = l_Lean_NameSet_empty;
v___x_2624_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2616_, v_snd_2622_, v___x_2623_);
lean_inc(v_fst_2621_);
v___x_2625_ = l_Lean_NameSet_insert(v___x_2624_, v_fst_2621_);
lean_inc(v_snd_2622_);
v___x_2626_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2622_, v___x_2625_, v_b_2616_);
v___x_2627_ = ((size_t)1ULL);
v___x_2628_ = lean_usize_add(v_i_2615_, v___x_2627_);
v_i_2615_ = v___x_2628_;
v_b_2616_ = v___x_2626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2630_, lean_object* v_sz_2631_, lean_object* v_i_2632_, lean_object* v_b_2633_, lean_object* v___y_2634_){
_start:
{
size_t v_sz_boxed_2635_; size_t v_i_boxed_2636_; lean_object* v_res_2637_; 
v_sz_boxed_2635_ = lean_unbox_usize(v_sz_2631_);
lean_dec(v_sz_2631_);
v_i_boxed_2636_ = lean_unbox_usize(v_i_2632_);
lean_dec(v_i_2632_);
v_res_2637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2630_, v_sz_boxed_2635_, v_i_boxed_2636_, v_b_2633_);
lean_dec_ref(v_as_2630_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2638_, size_t v_sz_2639_, size_t v_i_2640_, lean_object* v_b_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_usize_dec_lt(v_i_2640_, v_sz_2639_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_b_2641_);
return v___x_2646_;
}
else
{
lean_object* v_a_2647_; size_t v_sz_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v_a_2647_ = lean_array_uget_borrowed(v_as_2638_, v_i_2640_);
v_sz_2648_ = lean_array_size(v_a_2647_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2647_, v_sz_2648_, v___x_2649_, v_b_2641_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; size_t v___x_2652_; size_t v___x_2653_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = ((size_t)1ULL);
v___x_2653_ = lean_usize_add(v_i_2640_, v___x_2652_);
v_i_2640_ = v___x_2653_;
v_b_2641_ = v_a_2651_;
goto _start;
}
else
{
return v___x_2650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2655_, lean_object* v_sz_2656_, lean_object* v_i_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
size_t v_sz_boxed_2662_; size_t v_i_boxed_2663_; lean_object* v_res_2664_; 
v_sz_boxed_2662_ = lean_unbox_usize(v_sz_2656_);
lean_dec(v_sz_2656_);
v_i_boxed_2663_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_res_2664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2655_, v_sz_boxed_2662_, v_i_boxed_2663_, v_b_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec_ref(v_as_2655_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2665_, size_t v_i_2666_, size_t v_stop_2667_, lean_object* v_b_2668_){
_start:
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_usize_dec_eq(v_i_2666_, v_stop_2667_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v_fst_2671_; lean_object* v_snd_2672_; lean_object* v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; 
v___x_2670_ = lean_array_uget_borrowed(v_as_2665_, v_i_2666_);
v_fst_2671_ = lean_ctor_get(v___x_2670_, 0);
v_snd_2672_ = lean_ctor_get(v___x_2670_, 1);
lean_inc(v_snd_2672_);
lean_inc(v_fst_2671_);
v___x_2673_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2671_, v_snd_2672_, v_b_2668_);
v___x_2674_ = ((size_t)1ULL);
v___x_2675_ = lean_usize_add(v_i_2666_, v___x_2674_);
v_i_2666_ = v___x_2675_;
v_b_2668_ = v___x_2673_;
goto _start;
}
else
{
return v_b_2668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2677_, lean_object* v_i_2678_, lean_object* v_stop_2679_, lean_object* v_b_2680_){
_start:
{
size_t v_i_boxed_2681_; size_t v_stop_boxed_2682_; lean_object* v_res_2683_; 
v_i_boxed_2681_ = lean_unbox_usize(v_i_2678_);
lean_dec(v_i_2678_);
v_stop_boxed_2682_ = lean_unbox_usize(v_stop_2679_);
lean_dec(v_stop_2679_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2677_, v_i_boxed_2681_, v_stop_boxed_2682_, v_b_2680_);
lean_dec_ref(v_as_2677_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2684_, size_t v_i_2685_, size_t v_stop_2686_, lean_object* v_b_2687_){
_start:
{
lean_object* v___y_2689_; uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_eq(v_i_2685_, v_stop_2686_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2694_ = lean_array_uget_borrowed(v_as_2684_, v_i_2685_);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_array_get_size(v___x_2694_);
v___x_2697_ = lean_nat_dec_lt(v___x_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
v___y_2689_ = v_b_2687_;
goto v___jp_2688_;
}
else
{
uint8_t v___x_2698_; 
v___x_2698_ = lean_nat_dec_le(v___x_2696_, v___x_2696_);
if (v___x_2698_ == 0)
{
if (v___x_2697_ == 0)
{
v___y_2689_ = v_b_2687_;
goto v___jp_2688_;
}
else
{
size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = lean_usize_of_nat(v___x_2696_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2694_, v___x_2699_, v___x_2700_, v_b_2687_);
v___y_2689_ = v___x_2701_;
goto v___jp_2688_;
}
}
else
{
size_t v___x_2702_; size_t v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = lean_usize_of_nat(v___x_2696_);
v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2694_, v___x_2702_, v___x_2703_, v_b_2687_);
v___y_2689_ = v___x_2704_;
goto v___jp_2688_;
}
}
}
else
{
return v_b_2687_;
}
v___jp_2688_:
{
size_t v___x_2690_; size_t v___x_2691_; 
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_add(v_i_2685_, v___x_2690_);
v_i_2685_ = v___x_2691_;
v_b_2687_ = v___y_2689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2705_, lean_object* v_i_2706_, lean_object* v_stop_2707_, lean_object* v_b_2708_){
_start:
{
size_t v_i_boxed_2709_; size_t v_stop_boxed_2710_; lean_object* v_res_2711_; 
v_i_boxed_2709_ = lean_unbox_usize(v_i_2706_);
lean_dec(v_i_2706_);
v_stop_boxed_2710_ = lean_unbox_usize(v_stop_2707_);
lean_dec(v_stop_2707_);
v_res_2711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2705_, v_i_boxed_2709_, v_stop_boxed_2710_, v_b_2708_);
lean_dec_ref(v_as_2705_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v_env_2715_; lean_object* v___x_2716_; lean_object* v_ext_2717_; lean_object* v_toEnvExtension_2718_; lean_object* v_asyncMode_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v_categories_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2714_ = lean_st_ref_get(v___y_2712_);
v_env_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc_ref_n(v_env_2715_, 2);
lean_dec(v___x_2714_);
v___x_2716_ = l_Lean_Parser_parserExtension;
v_ext_2717_ = lean_ctor_get(v___x_2716_, 1);
v_toEnvExtension_2718_ = lean_ctor_get(v_ext_2717_, 0);
v_asyncMode_2719_ = lean_ctor_get(v_toEnvExtension_2718_, 2);
v___x_2720_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2721_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2720_, v___x_2716_, v_env_2715_, v_asyncMode_2719_);
v_categories_2722_ = lean_ctor_get(v___x_2721_, 2);
lean_inc_ref(v_categories_2722_);
lean_dec(v___x_2721_);
v___x_2723_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2724_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2722_, v___x_2723_);
lean_dec_ref(v_categories_2722_);
if (lean_obj_tag(v___x_2724_) == 1)
{
lean_object* v_val_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2762_; 
v_val_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2762_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_val_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2762_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___y_2730_; lean_object* v___x_2739_; lean_object* v_toEnvExtension_2740_; lean_object* v_exportEntriesFn_2741_; lean_object* v_asyncMode_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v_importedEntries_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v_exported_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2739_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2740_ = lean_ctor_get(v___x_2739_, 0);
v_exportEntriesFn_2741_ = lean_ctor_get(v___x_2739_, 4);
v_asyncMode_2742_ = lean_ctor_get(v_toEnvExtension_2740_, 2);
v___x_2743_ = lean_box(1);
v___x_2744_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2745_ = lean_box(0);
lean_inc_ref_n(v_env_2715_, 2);
v___x_2746_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2744_, v_toEnvExtension_2740_, v_env_2715_, v_asyncMode_2742_, v___x_2745_);
v_importedEntries_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc_ref(v_importedEntries_2747_);
lean_dec(v___x_2746_);
v___x_2748_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2743_, v___x_2739_, v_env_2715_, v_asyncMode_2742_, v___x_2745_);
lean_inc_ref(v_exportEntriesFn_2741_);
v___x_2749_ = lean_apply_2(v_exportEntriesFn_2741_, v_env_2715_, v___x_2748_);
v_exported_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_exported_2750_);
lean_dec_ref(v___x_2749_);
v___x_2751_ = lean_array_push(v_importedEntries_2747_, v_exported_2750_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_array_get_size(v___x_2751_);
v___x_2754_ = lean_nat_dec_lt(v___x_2752_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_dec_ref(v___x_2751_);
v___y_2730_ = v___x_2743_;
goto v___jp_2729_;
}
else
{
uint8_t v___x_2755_; 
v___x_2755_ = lean_nat_dec_le(v___x_2753_, v___x_2753_);
if (v___x_2755_ == 0)
{
if (v___x_2754_ == 0)
{
lean_dec_ref(v___x_2751_);
v___y_2730_ = v___x_2743_;
goto v___jp_2729_;
}
else
{
size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = lean_usize_of_nat(v___x_2753_);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2751_, v___x_2756_, v___x_2757_, v___x_2743_);
lean_dec_ref(v___x_2751_);
v___y_2730_ = v___x_2758_;
goto v___jp_2729_;
}
}
else
{
size_t v___x_2759_; size_t v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = lean_usize_of_nat(v___x_2753_);
v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2751_, v___x_2759_, v___x_2760_, v___x_2743_);
lean_dec_ref(v___x_2751_);
v___y_2730_ = v___x_2761_;
goto v___jp_2729_;
}
}
v___jp_2729_:
{
lean_object* v_tables_2731_; lean_object* v_leadingTable_2732_; lean_object* v_trailingTable_2733_; lean_object* v_firstTokens_2734_; lean_object* v_firstTokens_2735_; lean_object* v___x_2737_; 
v_tables_2731_ = lean_ctor_get(v_val_2725_, 2);
v_leadingTable_2732_ = lean_ctor_get(v_tables_2731_, 0);
v_trailingTable_2733_ = lean_ctor_get(v_tables_2731_, 2);
lean_inc(v_trailingTable_2733_);
lean_inc(v_leadingTable_2732_);
lean_inc(v_val_2725_);
v_firstTokens_2734_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2725_, v_leadingTable_2732_, v___y_2730_);
v_firstTokens_2735_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2725_, v_trailingTable_2733_, v_firstTokens_2734_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set_tag(v___x_2727_, 0);
lean_ctor_set(v___x_2727_, 0, v_firstTokens_2735_);
v___x_2737_ = v___x_2727_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_firstTokens_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v___x_2724_);
lean_dec_ref(v_env_2715_);
v___x_2763_ = lean_box(1);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2765_);
lean_dec(v___y_2765_);
return v_res_2767_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_box(1);
v___x_2769_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v_env_2779_; lean_object* v_env_2780_; lean_object* v_env_2781_; lean_object* v___x_2782_; lean_object* v_toEnvExtension_2783_; lean_object* v_exportEntriesFn_2784_; lean_object* v_asyncMode_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_importedEntries_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2842_; 
v___x_2776_ = lean_st_ref_get(v_a_2774_);
v___x_2777_ = lean_st_ref_get(v_a_2774_);
v___x_2778_ = lean_st_ref_get(v_a_2774_);
v_env_2779_ = lean_ctor_get(v___x_2776_, 0);
lean_inc_ref(v_env_2779_);
lean_dec(v___x_2776_);
v_env_2780_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_env_2780_);
lean_dec(v___x_2777_);
v_env_2781_ = lean_ctor_get(v___x_2778_, 0);
lean_inc_ref(v_env_2781_);
lean_dec(v___x_2778_);
v___x_2782_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2783_ = lean_ctor_get(v___x_2782_, 0);
v_exportEntriesFn_2784_ = lean_ctor_get(v___x_2782_, 4);
v_asyncMode_2785_ = lean_ctor_get(v_toEnvExtension_2783_, 2);
v___x_2786_ = lean_box(1);
v___x_2787_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2788_ = lean_box(0);
v___x_2789_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2787_, v_toEnvExtension_2783_, v_env_2779_, v_asyncMode_2785_, v___x_2788_);
v_importedEntries_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v___x_2789_, 1);
lean_dec(v_unused_2843_);
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2842_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_importedEntries_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2842_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v_exported_2796_; lean_object* v___x_2797_; size_t v_sz_2798_; size_t v___x_2799_; lean_object* v___x_2800_; 
v___x_2794_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2786_, v___x_2782_, v_env_2781_, v_asyncMode_2785_, v___x_2788_);
lean_inc_ref(v_exportEntriesFn_2784_);
v___x_2795_ = lean_apply_2(v_exportEntriesFn_2784_, v_env_2780_, v___x_2794_);
v_exported_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_exported_2796_);
lean_dec_ref(v___x_2795_);
v___x_2797_ = lean_array_push(v_importedEntries_2790_, v_exported_2796_);
v_sz_2798_ = lean_array_size(v___x_2797_);
v___x_2799_ = ((size_t)0ULL);
v___x_2800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2797_, v_sz_2798_, v___x_2799_, v___x_2786_, v_a_2773_, v_a_2774_);
lean_dec_ref(v___x_2797_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; lean_object* v_a_2803_; lean_object* v___x_2804_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2802_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2774_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref(v___x_2802_);
v___x_2804_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = lean_box(0);
v___x_2807_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2803_, v_a_2801_, v_a_2805_, v___x_2806_, v_a_2773_, v_a_2774_);
lean_dec(v_a_2801_);
lean_dec(v_a_2803_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2810_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2811_ = l_Lean_MessageData_joinSep(v_a_2808_, v___x_2810_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 7);
lean_ctor_set(v___x_2792_, 1, v___x_2811_);
lean_ctor_set(v___x_2792_, 0, v___x_2810_);
v___x_2813_ = v___x_2792_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = l_Lean_MessageData_nestD(v___x_2813_);
v___x_2815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2809_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2815_, v_a_2773_, v_a_2774_);
return v___x_2816_;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2792_);
v_a_2818_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2807_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2807_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2803_);
lean_dec(v_a_2801_);
lean_del_object(v___x_2792_);
v_a_2826_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2804_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2804_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_del_object(v___x_2792_);
v_a_2834_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2800_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2800_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2849_, v_a_2850_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v___stx_2853_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2858_, lean_object* v_t_2859_, lean_object* v_k_2860_, lean_object* v_fallback_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2859_, v_k_2860_, v_fallback_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2863_, lean_object* v_t_2864_, lean_object* v_k_2865_, lean_object* v_fallback_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2863_, v_t_2864_, v_k_2865_, v_fallback_2866_);
lean_dec(v_fallback_2866_);
lean_dec(v_k_2865_);
lean_dec(v_t_2864_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2868_, size_t v_sz_2869_, size_t v_i_2870_, lean_object* v_b_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2868_, v_sz_2869_, v_i_2870_, v_b_2871_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2876_, lean_object* v_sz_2877_, lean_object* v_i_2878_, lean_object* v_b_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
size_t v_sz_boxed_2883_; size_t v_i_boxed_2884_; lean_object* v_res_2885_; 
v_sz_boxed_2883_ = lean_unbox_usize(v_sz_2877_);
lean_dec(v_sz_2877_);
v_i_boxed_2884_ = lean_unbox_usize(v_i_2878_);
lean_dec(v_i_2878_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2876_, v_sz_boxed_2883_, v_i_boxed_2884_, v_b_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v_as_2876_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2894_, lean_object* v___x_2895_, lean_object* v___x_2896_, lean_object* v_inst_2897_, lean_object* v_R_2898_, lean_object* v_a_2899_, lean_object* v_b_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2894_, v___x_2895_, v___x_2896_, v_a_2899_, v_b_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2902_, lean_object* v___x_2903_, lean_object* v___x_2904_, lean_object* v_inst_2905_, lean_object* v_R_2906_, lean_object* v_a_2907_, lean_object* v_b_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2902_, v___x_2903_, v___x_2904_, v_inst_2905_, v_R_2906_, v_a_2907_, v_b_2908_);
lean_dec_ref(v___x_2903_);
lean_dec_ref(v_val_2902_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2910_, lean_object* v_t_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2910_, v_t_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2913_, lean_object* v_as_2914_, lean_object* v_lo_2915_, lean_object* v_hi_2916_, lean_object* v_w_2917_, lean_object* v_hlo_2918_, lean_object* v_hhi_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2913_, v_as_2914_, v_lo_2915_, v_hi_2916_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2921_, lean_object* v_as_2922_, lean_object* v_lo_2923_, lean_object* v_hi_2924_, lean_object* v_w_2925_, lean_object* v_hlo_2926_, lean_object* v_hhi_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2921_, v_as_2922_, v_lo_2923_, v_hi_2924_, v_w_2925_, v_hlo_2926_, v_hhi_2927_);
lean_dec(v_hi_2924_);
lean_dec(v_n_2921_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2930_, v_x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2933_, v_x_2934_, v_x_2935_);
lean_dec(v_x_2935_);
lean_dec_ref(v_x_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2937_, v___y_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2947_, lean_object* v_t_2948_, lean_object* v_k_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2948_, v_k_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2951_, lean_object* v_t_2952_, lean_object* v_k_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2951_, v_t_2952_, v_k_2953_);
lean_dec(v_k_2953_);
lean_dec(v_t_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2956_, v_x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2959_, lean_object* v_x_2960_, lean_object* v_x_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2959_, v_x_2960_, v_x_2961_);
lean_dec(v_x_2961_);
lean_dec_ref(v_x_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2963_, lean_object* v_lo_2964_, lean_object* v_hi_2965_, lean_object* v_hhi_2966_, lean_object* v_pivot_2967_, lean_object* v_as_2968_, lean_object* v_i_2969_, lean_object* v_k_2970_, lean_object* v_ilo_2971_, lean_object* v_ik_2972_, lean_object* v_w_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2965_, v_pivot_2967_, v_as_2968_, v_i_2969_, v_k_2970_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2975_, lean_object* v_lo_2976_, lean_object* v_hi_2977_, lean_object* v_hhi_2978_, lean_object* v_pivot_2979_, lean_object* v_as_2980_, lean_object* v_i_2981_, lean_object* v_k_2982_, lean_object* v_ilo_2983_, lean_object* v_ik_2984_, lean_object* v_w_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2975_, v_lo_2976_, v_hi_2977_, v_hhi_2978_, v_pivot_2979_, v_as_2980_, v_i_2981_, v_k_2982_, v_ilo_2983_, v_ik_2984_, v_w_2985_);
lean_dec(v_hi_2977_);
lean_dec(v_lo_2976_);
lean_dec(v_n_2975_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2987_, size_t v_sz_2988_, size_t v_i_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2987_, v_sz_2988_, v_i_2989_, v_b_2990_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2995_, lean_object* v_sz_2996_, lean_object* v_i_2997_, lean_object* v_b_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
size_t v_sz_boxed_3002_; size_t v_i_boxed_3003_; lean_object* v_res_3004_; 
v_sz_boxed_3002_ = lean_unbox_usize(v_sz_2996_);
lean_dec(v_sz_2996_);
v_i_boxed_3003_ = lean_unbox_usize(v_i_2997_);
lean_dec(v_i_2997_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2995_, v_sz_boxed_3002_, v_i_boxed_3003_, v_b_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_as_2995_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_3005_, lean_object* v_t_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_3005_, v_t_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_3008_, lean_object* v_t_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_3008_, v_t_3009_);
lean_dec(v_t_3009_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_3011_, lean_object* v_as_3012_, lean_object* v_lo_3013_, lean_object* v_hi_3014_, lean_object* v_w_3015_, lean_object* v_hlo_3016_, lean_object* v_hhi_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3011_, v_as_3012_, v_lo_3013_, v_hi_3014_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3019_, lean_object* v_as_3020_, lean_object* v_lo_3021_, lean_object* v_hi_3022_, lean_object* v_w_3023_, lean_object* v_hlo_3024_, lean_object* v_hhi_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3019_, v_as_3020_, v_lo_3021_, v_hi_3022_, v_w_3023_, v_hlo_3024_, v_hhi_3025_);
lean_dec(v_hi_3022_);
lean_dec(v_n_3019_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3027_, lean_object* v_x_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3027_, v_x_3028_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3033_, lean_object* v_x_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3033_, v_x_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3039_, lean_object* v_x_3040_, size_t v_x_3041_, lean_object* v_x_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3040_, v_x_3041_, v_x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
size_t v_x_19099__boxed_3048_; lean_object* v_res_3049_; 
v_x_19099__boxed_3048_ = lean_unbox_usize(v_x_3046_);
lean_dec(v_x_3046_);
v_res_3049_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3044_, v_x_3045_, v_x_19099__boxed_3048_, v_x_3047_);
lean_dec(v_x_3047_);
lean_dec_ref(v_x_3045_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3050_, lean_object* v_k_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v_x_3054_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3050_, v_k_3051_, v_x_3052_, v_x_3053_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3056_, lean_object* v_k_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v_x_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3056_, v_k_3057_, v_x_3058_, v_x_3059_, v_x_3060_);
lean_dec_ref(v_k_3057_);
lean_dec_ref(v_as_3056_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3062_, lean_object* v_m_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3063_, v_a_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3066_, lean_object* v_m_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3066_, v_m_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_m_3067_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3070_, lean_object* v_lo_3071_, lean_object* v_hi_3072_, lean_object* v_hhi_3073_, lean_object* v_pivot_3074_, lean_object* v_as_3075_, lean_object* v_i_3076_, lean_object* v_k_3077_, lean_object* v_ilo_3078_, lean_object* v_ik_3079_, lean_object* v_w_3080_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3072_, v_pivot_3074_, v_as_3075_, v_i_3076_, v_k_3077_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3082_, lean_object* v_lo_3083_, lean_object* v_hi_3084_, lean_object* v_hhi_3085_, lean_object* v_pivot_3086_, lean_object* v_as_3087_, lean_object* v_i_3088_, lean_object* v_k_3089_, lean_object* v_ilo_3090_, lean_object* v_ik_3091_, lean_object* v_w_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3082_, v_lo_3083_, v_hi_3084_, v_hhi_3085_, v_pivot_3086_, v_as_3087_, v_i_3088_, v_k_3089_, v_ilo_3090_, v_ik_3091_, v_w_3092_);
lean_dec(v_hi_3084_);
lean_dec(v_lo_3083_);
lean_dec(v_n_3082_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3094_, lean_object* v_keys_3095_, lean_object* v_vals_3096_, lean_object* v_heq_3097_, lean_object* v_i_3098_, lean_object* v_k_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3095_, v_vals_3096_, v_i_3098_, v_k_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3101_, lean_object* v_keys_3102_, lean_object* v_vals_3103_, lean_object* v_heq_3104_, lean_object* v_i_3105_, lean_object* v_k_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3101_, v_keys_3102_, v_vals_3103_, v_heq_3104_, v_i_3105_, v_k_3106_);
lean_dec(v_k_3106_);
lean_dec_ref(v_vals_3103_);
lean_dec_ref(v_keys_3102_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3108_, lean_object* v_a_3109_, lean_object* v_x_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3109_, v_x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3112_, lean_object* v_a_3113_, lean_object* v_x_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3112_, v_a_3113_, v_x_3114_);
lean_dec(v_x_3114_);
lean_dec(v_a_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3130_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3131_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3133_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3134_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3130_, v___x_3131_, v___x_3132_, v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3141_ = l_Lean_addBuiltinDocString(v___x_3139_, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3172_ = l_Lean_addBuiltinDeclarationRanges(v___x_3170_, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, uint8_t v_includeUnnamed_3178_, lean_object* v_x_3179_, lean_object* v_____s_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_fst_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3239_; 
v_fst_3186_ = lean_ctor_get(v_x_3179_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_x_3179_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_x_3179_, 1);
lean_dec(v_unused_3240_);
v___x_3188_ = v_x_3179_;
v_isShared_3189_ = v_isSharedCheck_3239_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_fst_3186_);
lean_dec(v_x_3179_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3239_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_userName_3191_; lean_object* v___y_3192_; lean_object* v___x_3224_; 
lean_inc(v_fst_3186_);
lean_inc_ref(v_env_3175_);
v___x_3224_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3175_, v_fst_3186_);
if (lean_obj_tag(v___x_3224_) == 1)
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3232_; 
lean_del_object(v___x_3188_);
lean_dec(v_fst_3186_);
lean_dec_ref(v_env_3175_);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3224_, 0);
lean_dec(v_unused_3233_);
v___x_3226_ = v___x_3224_;
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v___x_3224_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v_____s_3180_);
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_____s_3180_);
v___x_3229_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
}
else
{
lean_object* v___x_3234_; 
lean_dec(v___x_3224_);
v___x_3234_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3177_, v_fst_3186_);
if (lean_obj_tag(v___x_3234_) == 1)
{
lean_object* v_val_3235_; 
v_val_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v_userName_3191_ = v_val_3235_;
v___y_3192_ = v___y_3183_;
goto v___jp_3190_;
}
else
{
lean_dec(v___x_3234_);
if (v_includeUnnamed_3178_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_del_object(v___x_3188_);
lean_dec(v_fst_3186_);
lean_dec_ref(v_env_3175_);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v_____s_3180_);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; 
lean_inc(v_fst_3186_);
v___x_3238_ = l_Lean_Name_toString(v_fst_3186_, v_includeUnnamed_3178_);
v_userName_3191_ = v___x_3238_;
v___y_3192_ = v___y_3183_;
goto v___jp_3190_;
}
}
}
v___jp_3190_:
{
uint8_t v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = 1;
lean_inc(v_fst_3186_);
lean_inc_ref(v_env_3175_);
v___x_3194_ = l_Lean_findDocString_x3f(v_env_3175_, v_fst_3186_, v___x_3193_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3188_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3208_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3199_ = l_Lean_NameSet_empty;
v___x_3200_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3176_, v_fst_3186_, v___x_3199_);
lean_inc(v_fst_3186_);
v___x_3201_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3175_, v_fst_3186_);
v___x_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3202_, 0, v_fst_3186_);
lean_ctor_set(v___x_3202_, 1, v_userName_3191_);
lean_ctor_set(v___x_3202_, 2, v___x_3200_);
lean_ctor_set(v___x_3202_, 3, v_a_3195_);
lean_ctor_set(v___x_3202_, 4, v___x_3201_);
v___x_3203_ = lean_array_push(v_____s_3180_, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3204_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v_userName_3191_);
lean_dec(v_fst_3186_);
lean_dec_ref(v_____s_3180_);
lean_dec_ref(v_env_3175_);
v_a_3209_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3211_ = v___x_3194_;
v_isShared_3212_ = v_isSharedCheck_3223_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3194_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3223_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_ref_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
v_ref_3213_ = lean_ctor_get(v___y_3192_, 5);
v___x_3214_ = lean_io_error_to_string(v_a_3209_);
v___x_3215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
v___x_3216_ = l_Lean_MessageData_ofFormat(v___x_3215_);
lean_inc(v_ref_3213_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v___x_3216_);
lean_ctor_set(v___x_3188_, 0, v_ref_3213_);
v___x_3218_ = v___x_3188_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_ref_3213_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3220_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3218_);
v___x_3220_ = v___x_3211_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_includeUnnamed_3244_, lean_object* v_x_3245_, lean_object* v_____s_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
uint8_t v_includeUnnamed_boxed_3252_; lean_object* v_res_3253_; 
v_includeUnnamed_boxed_3252_ = lean_unbox(v_includeUnnamed_3244_);
v_res_3253_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3241_, v_a_3242_, v_a_3243_, v_includeUnnamed_boxed_3252_, v_x_3245_, v_____s_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v_a_3243_);
lean_dec(v_a_3242_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3254_, size_t v_sz_3255_, size_t v_i_3256_, lean_object* v_b_3257_){
_start:
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_usize_dec_lt(v_i_3256_, v_sz_3255_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_b_3257_);
return v___x_3260_;
}
else
{
lean_object* v_a_3261_; lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; size_t v___x_3268_; size_t v___x_3269_; 
v_a_3261_ = lean_array_uget_borrowed(v_as_3254_, v_i_3256_);
v_fst_3262_ = lean_ctor_get(v_a_3261_, 0);
v_snd_3263_ = lean_ctor_get(v_a_3261_, 1);
v___x_3264_ = l_Lean_NameSet_empty;
v___x_3265_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3257_, v_fst_3262_, v___x_3264_);
lean_inc(v_snd_3263_);
v___x_3266_ = l_Lean_NameSet_insert(v___x_3265_, v_snd_3263_);
lean_inc(v_fst_3262_);
v___x_3267_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3262_, v___x_3266_, v_b_3257_);
v___x_3268_ = ((size_t)1ULL);
v___x_3269_ = lean_usize_add(v_i_3256_, v___x_3268_);
v_i_3256_ = v___x_3269_;
v_b_3257_ = v___x_3267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3271_, lean_object* v_sz_3272_, lean_object* v_i_3273_, lean_object* v_b_3274_, lean_object* v___y_3275_){
_start:
{
size_t v_sz_boxed_3276_; size_t v_i_boxed_3277_; lean_object* v_res_3278_; 
v_sz_boxed_3276_ = lean_unbox_usize(v_sz_3272_);
lean_dec(v_sz_3272_);
v_i_boxed_3277_ = lean_unbox_usize(v_i_3273_);
lean_dec(v_i_3273_);
v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3271_, v_sz_boxed_3276_, v_i_boxed_3277_, v_b_3274_);
lean_dec_ref(v_as_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3279_, size_t v_sz_3280_, size_t v_i_3281_, lean_object* v_b_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_usize_dec_lt(v_i_3281_, v_sz_3280_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3289_, 0, v_b_3282_);
return v___x_3289_;
}
else
{
lean_object* v_a_3290_; size_t v_sz_3291_; size_t v___x_3292_; lean_object* v___x_3293_; 
v_a_3290_ = lean_array_uget_borrowed(v_as_3279_, v_i_3281_);
v_sz_3291_ = lean_array_size(v_a_3290_);
v___x_3292_ = ((size_t)0ULL);
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3290_, v_sz_3291_, v___x_3292_, v_b_3282_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; size_t v___x_3295_; size_t v___x_3296_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3293_, 1);
v___x_3295_ = ((size_t)1ULL);
v___x_3296_ = lean_usize_add(v_i_3281_, v___x_3295_);
v_i_3281_ = v___x_3296_;
v_b_3282_ = v_a_3294_;
goto _start;
}
else
{
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3298_, lean_object* v_sz_3299_, lean_object* v_i_3300_, lean_object* v_b_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
size_t v_sz_boxed_3307_; size_t v_i_boxed_3308_; lean_object* v_res_3309_; 
v_sz_boxed_3307_ = lean_unbox_usize(v_sz_3299_);
lean_dec(v_sz_3299_);
v_i_boxed_3308_ = lean_unbox_usize(v_i_3300_);
lean_dec(v_i_3300_);
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3298_, v_sz_boxed_3307_, v_i_boxed_3308_, v_b_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec_ref(v_as_3298_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3310_, lean_object* v_keys_3311_, lean_object* v_vals_3312_, lean_object* v_i_3313_, lean_object* v_acc_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = lean_array_get_size(v_keys_3311_);
v___x_3321_ = lean_nat_dec_lt(v_i_3313_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_dec(v_i_3313_);
lean_dec_ref(v_f_3310_);
v___x_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_acc_3314_);
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
return v___x_3323_;
}
else
{
lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v___x_3326_; 
v_k_3324_ = lean_array_fget_borrowed(v_keys_3311_, v_i_3313_);
v_v_3325_ = lean_array_fget_borrowed(v_vals_3312_, v_i_3313_);
lean_inc_ref(v_f_3310_);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3317_);
lean_inc(v___y_3316_);
lean_inc_ref(v___y_3315_);
lean_inc(v_v_3325_);
lean_inc(v_k_3324_);
v___x_3326_ = lean_apply_8(v_f_3310_, v_acc_3314_, v_k_3324_, v_v_3325_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, lean_box(0));
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
if (lean_obj_tag(v_a_3327_) == 0)
{
lean_dec_ref_known(v_a_3327_, 1);
lean_dec(v_i_3313_);
lean_dec_ref(v_f_3310_);
return v___x_3326_;
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec_ref_known(v___x_3326_, 1);
v_a_3328_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v_a_3327_, 1);
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = lean_nat_add(v_i_3313_, v___x_3329_);
lean_dec(v_i_3313_);
v_i_3313_ = v___x_3330_;
v_acc_3314_ = v_a_3328_;
goto _start;
}
}
else
{
lean_dec(v_i_3313_);
lean_dec_ref(v_f_3310_);
return v___x_3326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3332_, lean_object* v_keys_3333_, lean_object* v_vals_3334_, lean_object* v_i_3335_, lean_object* v_acc_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3332_, v_keys_3333_, v_vals_3334_, v_i_3335_, v_acc_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v_vals_3334_);
lean_dec_ref(v_keys_3333_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
if (lean_obj_tag(v_x_3344_) == 0)
{
lean_object* v_es_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3373_; 
v_es_3351_ = lean_ctor_get(v_x_3344_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_x_3344_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3353_ = v_x_3344_;
v_isShared_3354_ = v_isSharedCheck_3373_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_es_3351_);
lean_dec(v_x_3344_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3373_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = lean_array_get_size(v_es_3351_);
v___x_3357_ = lean_nat_dec_lt(v___x_3355_, v___x_3356_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3359_; 
lean_dec_ref(v_es_3351_);
lean_dec_ref(v_f_3343_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 1);
lean_ctor_set(v___x_3353_, 0, v_x_3345_);
v___x_3359_ = v___x_3353_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_x_3345_);
v___x_3359_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
}
else
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_nat_dec_le(v___x_3356_, v___x_3356_);
if (v___x_3362_ == 0)
{
if (v___x_3357_ == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref(v_es_3351_);
lean_dec_ref(v_f_3343_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set_tag(v___x_3353_, 1);
lean_ctor_set(v___x_3353_, 0, v_x_3345_);
v___x_3364_ = v___x_3353_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_x_3345_);
v___x_3364_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
return v___x_3365_;
}
}
else
{
size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
lean_del_object(v___x_3353_);
v___x_3367_ = ((size_t)0ULL);
v___x_3368_ = lean_usize_of_nat(v___x_3356_);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3343_, v_es_3351_, v___x_3367_, v___x_3368_, v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v_es_3351_);
return v___x_3369_;
}
}
else
{
size_t v___x_3370_; size_t v___x_3371_; lean_object* v___x_3372_; 
lean_del_object(v___x_3353_);
v___x_3370_ = ((size_t)0ULL);
v___x_3371_ = lean_usize_of_nat(v___x_3356_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3343_, v_es_3351_, v___x_3370_, v___x_3371_, v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v_es_3351_);
return v___x_3372_;
}
}
}
}
else
{
lean_object* v_ks_3374_; lean_object* v_vs_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_ks_3374_ = lean_ctor_get(v_x_3344_, 0);
lean_inc_ref(v_ks_3374_);
v_vs_3375_ = lean_ctor_get(v_x_3344_, 1);
lean_inc_ref(v_vs_3375_);
lean_dec_ref_known(v_x_3344_, 2);
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3343_, v_ks_3374_, v_vs_3375_, v___x_3376_, v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v_vs_3375_);
lean_dec_ref(v_ks_3374_);
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3378_, lean_object* v_as_3379_, size_t v_i_3380_, size_t v_stop_3381_, lean_object* v_b_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_a_3389_; lean_object* v___y_3394_; uint8_t v___x_3397_; 
v___x_3397_ = lean_usize_dec_eq(v_i_3380_, v_stop_3381_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_array_uget_borrowed(v_as_3379_, v_i_3380_);
switch(lean_obj_tag(v___x_3398_))
{
case 0:
{
lean_object* v_key_3399_; lean_object* v_val_3400_; lean_object* v___x_3401_; 
v_key_3399_ = lean_ctor_get(v___x_3398_, 0);
v_val_3400_ = lean_ctor_get(v___x_3398_, 1);
lean_inc_ref(v_f_3378_);
lean_inc(v___y_3386_);
lean_inc_ref(v___y_3385_);
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
lean_inc(v_val_3400_);
lean_inc(v_key_3399_);
v___x_3401_ = lean_apply_8(v_f_3378_, v_b_3382_, v_key_3399_, v_val_3400_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, lean_box(0));
v___y_3394_ = v___x_3401_;
goto v___jp_3393_;
}
case 1:
{
lean_object* v_node_3402_; lean_object* v___x_3403_; 
v_node_3402_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_node_3402_);
lean_inc_ref(v_f_3378_);
v___x_3403_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3378_, v_node_3402_, v_b_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
v___y_3394_ = v___x_3403_;
goto v___jp_3393_;
}
default: 
{
v_a_3389_ = v_b_3382_;
goto v___jp_3388_;
}
}
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref(v_f_3378_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v_b_3382_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
v___jp_3388_:
{
size_t v___x_3390_; size_t v___x_3391_; 
v___x_3390_ = ((size_t)1ULL);
v___x_3391_ = lean_usize_add(v_i_3380_, v___x_3390_);
v_i_3380_ = v___x_3391_;
v_b_3382_ = v_a_3389_;
goto _start;
}
v___jp_3393_:
{
if (lean_obj_tag(v___y_3394_) == 0)
{
lean_object* v_a_3395_; 
v_a_3395_ = lean_ctor_get(v___y_3394_, 0);
if (lean_obj_tag(v_a_3395_) == 0)
{
lean_dec_ref(v_f_3378_);
return v___y_3394_;
}
else
{
lean_object* v_a_3396_; 
lean_inc_ref(v_a_3395_);
lean_dec_ref_known(v___y_3394_, 1);
v_a_3396_ = lean_ctor_get(v_a_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v_a_3395_, 1);
v_a_3389_ = v_a_3396_;
goto v___jp_3388_;
}
}
else
{
lean_dec_ref(v_f_3378_);
return v___y_3394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3406_, lean_object* v_as_3407_, lean_object* v_i_3408_, lean_object* v_stop_3409_, lean_object* v_b_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
size_t v_i_boxed_3416_; size_t v_stop_boxed_3417_; lean_object* v_res_3418_; 
v_i_boxed_3416_ = lean_unbox_usize(v_i_3408_);
lean_dec(v_i_3408_);
v_stop_boxed_3417_ = lean_unbox_usize(v_stop_3409_);
lean_dec(v_stop_3409_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3406_, v_as_3407_, v_i_boxed_3416_, v_stop_boxed_3417_, v_b_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec_ref(v_as_3407_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3419_, lean_object* v_x_3420_, lean_object* v_x_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3419_, v_x_3420_, v_x_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3428_, lean_object* v_s_3429_, lean_object* v_a_3430_, lean_object* v_b_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_a_3430_);
lean_ctor_set(v___x_3437_, 1, v_b_3431_);
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
v___x_3438_ = lean_apply_7(v_f_3428_, v___x_3437_, v_s_3429_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, lean_box(0));
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3465_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3465_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3465_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
if (lean_obj_tag(v_a_3439_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3453_; 
v_a_3443_ = lean_ctor_get(v_a_3439_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3445_ = v_a_3439_;
v_isShared_3446_ = v_isSharedCheck_3453_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v_a_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3453_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3448_);
v___x_3450_ = v___x_3441_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3464_; 
v_a_3454_ = lean_ctor_get(v_a_3439_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_a_3439_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3456_ = v_a_3439_;
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v_a_3439_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3459_);
v___x_3461_ = v___x_3441_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
v_a_3466_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3438_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3438_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3474_, lean_object* v_s_3475_, lean_object* v_a_3476_, lean_object* v_b_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3474_, v_s_3475_, v_a_3476_, v_b_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3484_, lean_object* v_init_3485_, lean_object* v_f_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___f_3492_; lean_object* v___x_3493_; 
v___f_3492_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3492_, 0, v_f_3486_);
lean_inc_ref(v_map_3484_);
v___x_3493_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3492_, v_map_3484_, v_init_3485_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3502_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3502_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3502_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v_a_3498_; lean_object* v___x_3500_; 
v_a_3498_ = lean_ctor_get(v_a_3494_, 0);
lean_inc(v_a_3498_);
lean_dec(v_a_3494_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v_a_3498_);
v___x_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
v_a_3503_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3493_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3493_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3511_, lean_object* v_init_3512_, lean_object* v_f_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3511_, v_init_3512_, v_f_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v_map_3511_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; lean_object* v_env_3523_; lean_object* v___x_3524_; lean_object* v_ext_3525_; lean_object* v_toEnvExtension_3526_; lean_object* v_asyncMode_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_categories_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3522_ = lean_st_ref_get(v___y_3520_);
v_env_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_ref_n(v_env_3523_, 2);
lean_dec(v___x_3522_);
v___x_3524_ = l_Lean_Parser_parserExtension;
v_ext_3525_ = lean_ctor_get(v___x_3524_, 1);
v_toEnvExtension_3526_ = lean_ctor_get(v_ext_3525_, 0);
v_asyncMode_3527_ = lean_ctor_get(v_toEnvExtension_3526_, 2);
v___x_3528_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3529_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3528_, v___x_3524_, v_env_3523_, v_asyncMode_3527_);
v_categories_3530_ = lean_ctor_get(v___x_3529_, 2);
lean_inc_ref(v_categories_3530_);
lean_dec(v___x_3529_);
v___x_3531_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3532_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3530_, v___x_3531_);
lean_dec_ref(v_categories_3530_);
if (lean_obj_tag(v___x_3532_) == 1)
{
lean_object* v_val_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3570_; 
v_val_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3570_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_val_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3570_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___y_3538_; lean_object* v___x_3547_; lean_object* v_toEnvExtension_3548_; lean_object* v_exportEntriesFn_3549_; lean_object* v_asyncMode_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v_importedEntries_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v_exported_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3547_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3548_ = lean_ctor_get(v___x_3547_, 0);
v_exportEntriesFn_3549_ = lean_ctor_get(v___x_3547_, 4);
v_asyncMode_3550_ = lean_ctor_get(v_toEnvExtension_3548_, 2);
v___x_3551_ = lean_box(1);
v___x_3552_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3553_ = lean_box(0);
lean_inc_ref_n(v_env_3523_, 2);
v___x_3554_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3552_, v_toEnvExtension_3548_, v_env_3523_, v_asyncMode_3550_, v___x_3553_);
v_importedEntries_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc_ref(v_importedEntries_3555_);
lean_dec(v___x_3554_);
v___x_3556_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3551_, v___x_3547_, v_env_3523_, v_asyncMode_3550_, v___x_3553_);
lean_inc_ref(v_exportEntriesFn_3549_);
v___x_3557_ = lean_apply_2(v_exportEntriesFn_3549_, v_env_3523_, v___x_3556_);
v_exported_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_exported_3558_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = lean_array_push(v_importedEntries_3555_, v_exported_3558_);
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = lean_array_get_size(v___x_3559_);
v___x_3562_ = lean_nat_dec_lt(v___x_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
lean_dec_ref(v___x_3559_);
v___y_3538_ = v___x_3551_;
goto v___jp_3537_;
}
else
{
uint8_t v___x_3563_; 
v___x_3563_ = lean_nat_dec_le(v___x_3561_, v___x_3561_);
if (v___x_3563_ == 0)
{
if (v___x_3562_ == 0)
{
lean_dec_ref(v___x_3559_);
v___y_3538_ = v___x_3551_;
goto v___jp_3537_;
}
else
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)0ULL);
v___x_3565_ = lean_usize_of_nat(v___x_3561_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3559_, v___x_3564_, v___x_3565_, v___x_3551_);
lean_dec_ref(v___x_3559_);
v___y_3538_ = v___x_3566_;
goto v___jp_3537_;
}
}
else
{
size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = ((size_t)0ULL);
v___x_3568_ = lean_usize_of_nat(v___x_3561_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3559_, v___x_3567_, v___x_3568_, v___x_3551_);
lean_dec_ref(v___x_3559_);
v___y_3538_ = v___x_3569_;
goto v___jp_3537_;
}
}
v___jp_3537_:
{
lean_object* v_tables_3539_; lean_object* v_leadingTable_3540_; lean_object* v_trailingTable_3541_; lean_object* v_firstTokens_3542_; lean_object* v_firstTokens_3543_; lean_object* v___x_3545_; 
v_tables_3539_ = lean_ctor_get(v_val_3533_, 2);
v_leadingTable_3540_ = lean_ctor_get(v_tables_3539_, 0);
v_trailingTable_3541_ = lean_ctor_get(v_tables_3539_, 2);
lean_inc(v_trailingTable_3541_);
lean_inc(v_leadingTable_3540_);
lean_inc(v_val_3533_);
v_firstTokens_3542_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3533_, v_leadingTable_3540_, v___y_3538_);
v_firstTokens_3543_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3533_, v_trailingTable_3541_, v_firstTokens_3542_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set_tag(v___x_3535_, 0);
lean_ctor_set(v___x_3535_, 0, v_firstTokens_3543_);
v___x_3545_ = v___x_3535_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_firstTokens_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_dec(v___x_3532_);
lean_dec_ref(v_env_3523_);
v___x_3571_ = lean_box(1);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3573_);
lean_dec(v___y_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v___x_3584_; lean_object* v_env_3585_; lean_object* v___x_3586_; lean_object* v_toEnvExtension_3587_; lean_object* v_exportEntriesFn_3588_; lean_object* v_asyncMode_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_importedEntries_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_exported_3597_; lean_object* v___x_3598_; size_t v_sz_3599_; size_t v___x_3600_; lean_object* v___x_3601_; 
v___x_3584_ = lean_st_ref_get(v_a_3582_);
v_env_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc_ref_n(v_env_3585_, 4);
lean_dec(v___x_3584_);
v___x_3586_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3587_ = lean_ctor_get(v___x_3586_, 0);
v_exportEntriesFn_3588_ = lean_ctor_get(v___x_3586_, 4);
v_asyncMode_3589_ = lean_ctor_get(v_toEnvExtension_3587_, 2);
v___x_3590_ = lean_box(1);
v___x_3591_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3592_ = lean_box(0);
v___x_3593_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3591_, v_toEnvExtension_3587_, v_env_3585_, v_asyncMode_3589_, v___x_3592_);
v_importedEntries_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_ref(v_importedEntries_3594_);
lean_dec(v___x_3593_);
v___x_3595_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3590_, v___x_3586_, v_env_3585_, v_asyncMode_3589_, v___x_3592_);
lean_inc_ref(v_exportEntriesFn_3588_);
v___x_3596_ = lean_apply_2(v_exportEntriesFn_3588_, v_env_3585_, v___x_3595_);
v_exported_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_exported_3597_);
lean_dec_ref(v___x_3596_);
v___x_3598_ = lean_array_push(v_importedEntries_3594_, v_exported_3597_);
v_sz_3599_ = lean_array_size(v___x_3598_);
v___x_3600_ = ((size_t)0ULL);
v___x_3601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3598_, v_sz_3599_, v___x_3600_, v___x_3590_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
lean_dec_ref(v___x_3598_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3626_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3626_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3626_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v_ext_3607_; lean_object* v_toEnvExtension_3608_; lean_object* v_asyncMode_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_categories_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3606_ = l_Lean_Parser_parserExtension;
v_ext_3607_ = lean_ctor_get(v___x_3606_, 1);
v_toEnvExtension_3608_ = lean_ctor_get(v_ext_3607_, 0);
v_asyncMode_3609_ = lean_ctor_get(v_toEnvExtension_3608_, 2);
v___x_3610_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3585_);
v___x_3611_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3610_, v___x_3606_, v_env_3585_, v_asyncMode_3609_);
v_categories_3612_ = lean_ctor_get(v___x_3611_, 2);
lean_inc_ref(v_categories_3612_);
lean_dec(v___x_3611_);
v___x_3613_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3614_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3615_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3612_, v___x_3614_);
lean_dec_ref(v_categories_3612_);
if (lean_obj_tag(v___x_3615_) == 1)
{
lean_object* v_val_3616_; lean_object* v___x_3617_; lean_object* v_a_3618_; lean_object* v_kinds_3619_; lean_object* v___x_3620_; lean_object* v___f_3621_; lean_object* v___x_3622_; 
lean_del_object(v___x_3604_);
v_val_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_val_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3582_);
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3617_);
v_kinds_3619_ = lean_ctor_get(v_val_3616_, 1);
lean_inc_ref(v_kinds_3619_);
lean_dec(v_val_3616_);
v___x_3620_ = lean_box(v_includeUnnamed_3578_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3621_, 0, v_env_3585_);
lean_closure_set(v___f_3621_, 1, v_a_3602_);
lean_closure_set(v___f_3621_, 2, v_a_3618_);
lean_closure_set(v___f_3621_, 3, v___x_3620_);
v___x_3622_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3619_, v___x_3613_, v___f_3621_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
lean_dec_ref(v_kinds_3619_);
return v___x_3622_;
}
else
{
lean_object* v___x_3624_; 
lean_dec(v___x_3615_);
lean_dec(v_a_3602_);
lean_dec_ref(v_env_3585_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3613_);
v___x_3624_ = v___x_3604_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3613_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v_env_3585_);
v_a_3627_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3601_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3601_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
uint8_t v_includeUnnamed_boxed_3641_; lean_object* v_res_3642_; 
v_includeUnnamed_boxed_3641_ = lean_unbox(v_includeUnnamed_3635_);
v_res_3642_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3641_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3643_, size_t v_sz_3644_, size_t v_i_3645_, lean_object* v_b_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3643_, v_sz_3644_, v_i_3645_, v_b_3646_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3653_, lean_object* v_sz_3654_, lean_object* v_i_3655_, lean_object* v_b_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
size_t v_sz_boxed_3662_; size_t v_i_boxed_3663_; lean_object* v_res_3664_; 
v_sz_boxed_3662_ = lean_unbox_usize(v_sz_3654_);
lean_dec(v_sz_3654_);
v_i_boxed_3663_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_res_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3653_, v_sz_boxed_3662_, v_i_boxed_3663_, v_b_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec_ref(v_as_3653_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3668_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3677_, lean_object* v_00_u03b2_3678_, lean_object* v_map_3679_, lean_object* v_init_3680_, lean_object* v_f_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3679_, v_init_3680_, v_f_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3688_, lean_object* v_00_u03b2_3689_, lean_object* v_map_3690_, lean_object* v_init_3691_, lean_object* v_f_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3688_, v_00_u03b2_3689_, v_map_3690_, v_init_3691_, v_f_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v_map_3690_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3699_, lean_object* v_f_3700_, lean_object* v_init_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3700_, v_map_3699_, v_init_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3708_, lean_object* v_f_3709_, lean_object* v_init_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3708_, v_f_3709_, v_init_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3717_, lean_object* v_00_u03c3_3718_, lean_object* v_00_u03b2_3719_, lean_object* v_map_3720_, lean_object* v_f_3721_, lean_object* v_init_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3721_, v_map_3720_, v_init_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3729_, lean_object* v_00_u03c3_3730_, lean_object* v_00_u03b2_3731_, lean_object* v_map_3732_, lean_object* v_f_3733_, lean_object* v_init_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3729_, v_00_u03c3_3730_, v_00_u03b2_3731_, v_map_3732_, v_f_3733_, v_init_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3741_, lean_object* v_00_u03c3_3742_, lean_object* v_00_u03b1_3743_, lean_object* v_00_u03b2_3744_, lean_object* v_f_3745_, lean_object* v_x_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3745_, v_x_3746_, v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3754_, lean_object* v_00_u03c3_3755_, lean_object* v_00_u03b1_3756_, lean_object* v_00_u03b2_3757_, lean_object* v_f_3758_, lean_object* v_x_3759_, lean_object* v_x_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3754_, v_00_u03c3_3755_, v_00_u03b1_3756_, v_00_u03b2_3757_, v_f_3758_, v_x_3759_, v_x_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3767_, lean_object* v_00_u03b2_3768_, lean_object* v_00_u03c3_3769_, lean_object* v_00_u03c3_3770_, lean_object* v_f_3771_, lean_object* v_as_3772_, size_t v_i_3773_, size_t v_stop_3774_, lean_object* v_b_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3771_, v_as_3772_, v_i_3773_, v_stop_3774_, v_b_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_00_u03b2_3783_, lean_object* v_00_u03c3_3784_, lean_object* v_00_u03c3_3785_, lean_object* v_f_3786_, lean_object* v_as_3787_, lean_object* v_i_3788_, lean_object* v_stop_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
size_t v_i_boxed_3796_; size_t v_stop_boxed_3797_; lean_object* v_res_3798_; 
v_i_boxed_3796_ = lean_unbox_usize(v_i_3788_);
lean_dec(v_i_3788_);
v_stop_boxed_3797_ = lean_unbox_usize(v_stop_3789_);
lean_dec(v_stop_3789_);
v_res_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3782_, v_00_u03b2_3783_, v_00_u03c3_3784_, v_00_u03c3_3785_, v_f_3786_, v_as_3787_, v_i_boxed_3796_, v_stop_boxed_3797_, v_b_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_as_3787_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3799_, lean_object* v_00_u03c3_3800_, lean_object* v_00_u03b1_3801_, lean_object* v_00_u03b2_3802_, lean_object* v_f_3803_, lean_object* v_keys_3804_, lean_object* v_vals_3805_, lean_object* v_heq_3806_, lean_object* v_i_3807_, lean_object* v_acc_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3803_, v_keys_3804_, v_vals_3805_, v_i_3807_, v_acc_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3815_, lean_object* v_00_u03c3_3816_, lean_object* v_00_u03b1_3817_, lean_object* v_00_u03b2_3818_, lean_object* v_f_3819_, lean_object* v_keys_3820_, lean_object* v_vals_3821_, lean_object* v_heq_3822_, lean_object* v_i_3823_, lean_object* v_acc_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3815_, v_00_u03c3_3816_, v_00_u03b1_3817_, v_00_u03b2_3818_, v_f_3819_, v_keys_3820_, v_vals_3821_, v_heq_3822_, v_i_3823_, v_acc_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec_ref(v_vals_3821_);
lean_dec_ref(v_keys_3820_);
return v_res_3830_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
