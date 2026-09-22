// Lean compiler output
// Module: Lean.Attributes
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime;
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeApplicationTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeApplicationTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeApplicationTime___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeApplicationTime = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMonadLiftImportMAttrM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadLiftImportMAttrM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadLiftImportMAttrM___closed__0 = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instMonadLiftImportMAttrM = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__0 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__1 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__2 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__3 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__4 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value;
static const lean_array_object l_Lean_AttributeImplCore_ref___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__5 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__5_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__6 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__7 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__8 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__9 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__9_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__10 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__11 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__12;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__13;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__14 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__15 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__16 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__17 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__18;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__19;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__20;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__21;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__22;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__23;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__24;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__25;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__26;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__27;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_AttributeImplCore_ref___autoParam;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "instInhabitedAttributeImplCore"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 168, 67, 30, 9, 195, 195, 250)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 28, 76, 169, 127, 73, 161, 93)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__4 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore_default = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeKind___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeKind = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__1 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__2 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToStringAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToStringAttributeKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringAttributeKind___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringAttributeKind = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1;
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value)} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl_default = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeMapRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "Failed to register attribute: Attributes can only be registered during initialization"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__0 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__0_value;
static lean_once_cell_t l_Lean_registerBuiltinAttribute___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerBuiltinAttribute___closed__1;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Invalid builtin attribute declaration: `"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__2 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__2_value;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` has already been used"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__3 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Unexpected attribute argument: This attribute takes no arguments"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__4;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__5 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__6 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected attribute argument"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__4 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected identifier, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getAttrParamOptPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected a priority, but found"};
static const lean_object* l_Lean_getAttrParamOptPrio___closed__0 = (const lean_object*)&l_Lean_getAttrParamOptPrio___closed__0_value;
static lean_once_cell_t l_Lean_getAttrParamOptPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAttrParamOptPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Unexpected attribute argument: Expected an optional priority, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getPrio___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getPrio___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` must be public"};
static const lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` must be marked as `meta`"};
static const lean_object* l_Lean_ensureAttrDeclIsMeta___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsMeta___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsMeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsMeta___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tag attribute"};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value;
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__5 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerTagAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___closed__0_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___closed__1_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___closed__2_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__3, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___closed__3_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___closed__4_value;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__5;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__6;
static const lean_ctor_object l_Lean_registerTagAttribute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___closed__1_value)}};
static const lean_object* l_Lean_registerTagAttribute___closed__7 = (const lean_object*)&l_Lean_registerTagAttribute___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "parametric attribute"};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__4 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__5 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to add parametric attribute `["};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "]` to `"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`: Attribute has already been set"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: Declaration is in an imported module"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "enumeration attribute extension"};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__2_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__4 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__5 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__5_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__6___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__6 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__6_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__7 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__7_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__8 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Internal error calling `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__0 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__0_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ".setValue` for `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__1 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__1_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = ": Declaration is not from this async context `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__2 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__2_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__3 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__3_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__4 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__4_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__5 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__5_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": Attribute has already been set"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__6 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__6_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = ": Declaration is in an imported module"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__7 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeImplBuilderTableRef;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Attribute implementation builder `"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__0 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__0_value;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__1 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Unknown attribute implementation builder `"};
static const lean_object* l_Lean_mkAttributeImplOfEntry___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeExtensionState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Unexpected attribute implementation type: `{.ofConstName declName}` is not of type `Lean.AttributeImpl`"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value)}};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__1 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__2 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AttributeImpl"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__3 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "attributeExtension"};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 25, 250, 145, 208, 184, 170, 105)}};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_addAttrEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeExtension;
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames();
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object*);
static const lean_string_object l_Lean_getBuiltinAttributeImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unknown attribute `"};
static const lean_object* l_Lean_getBuiltinAttributeImpl___closed__0 = (const lean_object*)&l_Lean_getBuiltinAttributeImpl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_num_attributes();
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_23_){
_start:
{
lean_inc(v_afterTypeChecking_23_);
return v_afterTypeChecking_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_24_);
lean_dec(v_afterTypeChecking_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_afterTypeChecking_29_){
_start:
{
lean_inc(v_afterTypeChecking_29_);
return v_afterTypeChecking_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_afterTypeChecking_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_afterTypeChecking_33_);
lean_dec(v_afterTypeChecking_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_36_){
_start:
{
lean_inc(v_afterCompilation_36_);
return v_afterCompilation_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_37_);
lean_dec(v_afterCompilation_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_afterCompilation_42_){
_start:
{
lean_inc(v_afterCompilation_42_);
return v_afterCompilation_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_afterCompilation_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_afterCompilation_46_);
lean_dec(v_afterCompilation_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_49_){
_start:
{
lean_inc(v_beforeElaboration_49_);
return v_beforeElaboration_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_50_);
lean_dec(v_beforeElaboration_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_beforeElaboration_55_){
_start:
{
lean_inc(v_beforeElaboration_55_);
return v_beforeElaboration_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_beforeElaboration_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_beforeElaboration_59_);
lean_dec(v_beforeElaboration_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_AttributeApplicationTime_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_21__boxed_71_; uint8_t v_y_22__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_21__boxed_71_ = lean_unbox(v_x_69_);
v_y_22__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_21__boxed_71_, v_y_22__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_toCold_83_; lean_object* v_env_84_; lean_object* v_ref_85_; lean_object* v_options_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_toCold_83_ = lean_ctor_get(v___y_79_, 0);
v_env_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_82_);
v_ref_85_ = lean_ctor_get(v___y_79_, 2);
v_options_86_ = lean_ctor_get(v_toCold_83_, 2);
lean_inc_ref(v_options_86_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_env_84_);
lean_ctor_set(v___x_87_, 1, v_options_86_);
v___x_88_ = lean_apply_2(v_x_78_, v___x_87_, lean_box(0));
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v_a_97_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v___x_88_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_88_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_101_ = lean_io_error_to_string(v_a_97_);
v___x_102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = l_Lean_MessageData_ofFormat(v___x_102_);
lean_inc(v_ref_85_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_85_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_104_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_109_, v_x_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_144_ = l_Lean_mkAtom(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_146_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_157_ = l_Lean_mkAtom(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_159_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_160_ = lean_array_push(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_162_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_163_ = lean_box(2);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_166_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_169_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_173_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_176_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_180_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_183_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_187_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_190_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_191_ = lean_box(2);
v___x_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_208_){
_start:
{
switch(v_x_208_)
{
case 0:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(0u);
return v___x_209_;
}
case 1:
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(1u);
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(2u);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_212_){
_start:
{
uint8_t v_x_boxed_213_; lean_object* v_res_214_; 
v_x_boxed_213_ = lean_unbox(v_x_212_);
v_res_214_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_215_){
_start:
{
lean_inc(v_k_215_);
return v_k_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_216_);
lean_dec(v_k_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_218_, lean_object* v_ctorIdx_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_k_222_){
_start:
{
lean_inc(v_k_222_);
return v_k_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_AttributeKind_ctorElim(v_motive_223_, v_ctorIdx_224_, v_t_boxed_228_, v_h_226_, v_k_227_);
lean_dec(v_k_227_);
lean_dec(v_ctorIdx_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_230_){
_start:
{
lean_inc(v_global_230_);
return v_global_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_AttributeKind_global_elim___redArg(v_global_231_);
lean_dec(v_global_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_global_236_){
_start:
{
lean_inc(v_global_236_);
return v_global_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_global_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_AttributeKind_global_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_global_240_);
lean_dec(v_global_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_243_){
_start:
{
lean_inc(v_local_243_);
return v_local_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_AttributeKind_local_elim___redArg(v_local_244_);
lean_dec(v_local_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_local_249_){
_start:
{
lean_inc(v_local_249_);
return v_local_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_local_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_AttributeKind_local_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_local_253_);
lean_dec(v_local_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_256_){
_start:
{
lean_inc(v_scoped_256_);
return v_scoped_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_257_);
lean_dec(v_scoped_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_scoped_262_){
_start:
{
lean_inc(v_scoped_262_);
return v_scoped_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_scoped_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Lean_AttributeKind_scoped_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_scoped_266_);
lean_dec(v_scoped_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_269_, uint8_t v_y_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_x_269_);
v___x_272_ = l_Lean_AttributeKind_ctorIdx(v_y_270_);
v___x_273_ = lean_nat_dec_eq(v___x_271_, v___x_272_);
lean_dec(v___x_272_);
lean_dec(v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_274_, lean_object* v_y_275_){
_start:
{
uint8_t v_x_21__boxed_276_; uint8_t v_y_22__boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_x_21__boxed_276_ = lean_unbox(v_x_274_);
v_y_22__boxed_277_ = lean_unbox(v_y_275_);
v_res_278_ = l_Lean_instBEqAttributeKind_beq(v_x_21__boxed_276_, v_y_22__boxed_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_287_){
_start:
{
switch(v_x_287_)
{
case 0:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_288_;
}
case 1:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_289_;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_291_){
_start:
{
uint8_t v_x_36__boxed_292_; lean_object* v_res_293_; 
v_x_36__boxed_292_ = lean_unbox(v_x_291_);
v_res_293_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_292_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = l_Lean_instInhabitedMessageData_default;
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_299_, lean_object* v___y_300_, uint8_t v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
uint8_t v___y_1014__boxed_313_; lean_object* v_res_314_; 
v___y_1014__boxed_313_ = lean_unbox(v___y_309_);
v_res_314_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_307_, v___y_308_, v___y_1014__boxed_313_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_308_);
lean_dec(v_x_307_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_315_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
lean_ctor_set(v___x_320_, 3, v___x_319_);
lean_ctor_set(v___x_320_, 4, v___x_318_);
lean_ctor_set(v___x_320_, 5, v___x_318_);
lean_ctor_set(v___x_320_, 6, v___x_318_);
lean_ctor_set(v___x_320_, 7, v___x_318_);
lean_ctor_set(v___x_320_, 8, v___x_318_);
lean_ctor_set(v___x_320_, 9, v___x_318_);
lean_ctor_set(v___x_320_, 10, v___x_318_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(32u);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_324_ = ((size_t)5ULL);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_unsigned_to_nat(32u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_329_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_325_);
lean_ctor_set(v___x_329_, 3, v___x_325_);
lean_ctor_set_usize(v___x_329_, 4, v___x_324_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_330_ = lean_box(1);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
lean_ctor_set(v___x_333_, 2, v___x_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_toCold_339_; lean_object* v_env_340_; lean_object* v_options_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_338_ = lean_st_ref_get(v___y_336_);
v_toCold_339_ = lean_ctor_get(v___y_335_, 0);
v_env_340_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_env_340_);
lean_dec(v___x_338_);
v_options_341_ = lean_ctor_get(v_toCold_339_, 2);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_341_);
v___x_344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_344_, 0, v_env_340_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
lean_ctor_set(v___x_344_, 2, v___x_343_);
lean_ctor_set(v___x_344_, 3, v_options_341_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_msgData_334_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_ref_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_ref_356_ = lean_ctor_get(v___y_353_, 2);
v___x_357_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_352_, v___y_353_, v___y_354_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_inc(v_ref_356_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_356_);
lean_ctor_set(v___x_362_, 1, v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_378_, lean_object* v_decl_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_name_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_name_383_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_name_383_);
lean_dec_ref(v___x_378_);
v___x_384_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_385_ = l_Lean_MessageData_ofName(v_name_383_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_388_, v___y_380_, v___y_381_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_390_, lean_object* v_decl_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_390_, v_decl_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_decl_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_404_, lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_unsigned_to_nat(16u);
v___x_419_ = lean_mk_array(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_425_ = lean_st_mk_ref(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
else
{
lean_object* v_key_432_; lean_object* v_tail_433_; uint8_t v___x_434_; 
v_key_432_ = lean_ctor_get(v_x_430_, 0);
v_tail_433_ = lean_ctor_get(v_x_430_, 2);
v___x_434_ = lean_name_eq(v_key_432_, v_a_429_);
if (v___x_434_ == 0)
{
v_x_430_ = v_tail_433_;
goto _start;
}
else
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec(v_a_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_buckets_442_; lean_object* v___x_443_; uint64_t v___y_445_; 
v_buckets_442_ = lean_ctor_get(v_m_440_, 1);
v___x_443_ = lean_array_get_size(v_buckets_442_);
if (lean_obj_tag(v_a_441_) == 0)
{
uint64_t v___x_459_; 
v___x_459_ = 1723ULL;
v___y_445_ = v___x_459_;
goto v___jp_444_;
}
else
{
uint64_t v_hash_460_; 
v_hash_460_ = lean_ctor_get_uint64(v_a_441_, sizeof(void*)*2);
v___y_445_ = v_hash_460_;
goto v___jp_444_;
}
v___jp_444_:
{
uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_446_ = 32ULL;
v___x_447_ = lean_uint64_shift_right(v___y_445_, v___x_446_);
v_fold_448_ = lean_uint64_xor(v___y_445_, v___x_447_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_443_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v___x_457_ = lean_array_uget_borrowed(v_buckets_442_, v___x_456_);
v___x_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_441_, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_m_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
return v_x_467_;
}
else
{
lean_object* v_key_468_; lean_object* v_value_469_; lean_object* v_tail_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_key_468_ = lean_ctor_get(v_x_467_, 0);
v_value_469_ = lean_ctor_get(v_x_467_, 1);
v_tail_470_ = lean_ctor_get(v_x_467_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v_x_467_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_tail_470_);
lean_inc(v_value_469_);
lean_inc(v_key_468_);
lean_dec(v_x_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_name_eq(v_key_468_, v_a_465_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_465_, v_b_466_, v_tail_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_key_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_value_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_value_469_);
lean_dec(v_key_468_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_b_466_);
lean_ctor_set(v___x_472_, 0, v_a_465_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_b_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_tail_470_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
return v_x_483_;
}
else
{
lean_object* v_key_485_; lean_object* v_value_486_; lean_object* v_tail_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_513_; 
v_key_485_ = lean_ctor_get(v_x_484_, 0);
v_value_486_ = lean_ctor_get(v_x_484_, 1);
v_tail_487_ = lean_ctor_get(v_x_484_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_489_ = v_x_484_;
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_tail_487_);
lean_inc(v_value_486_);
lean_inc(v_key_485_);
lean_dec(v_x_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; uint64_t v___y_493_; 
v___x_491_ = lean_array_get_size(v_x_483_);
if (lean_obj_tag(v_key_485_) == 0)
{
uint64_t v___x_511_; 
v___x_511_ = 1723ULL;
v___y_493_ = v___x_511_;
goto v___jp_492_;
}
else
{
uint64_t v_hash_512_; 
v_hash_512_ = lean_ctor_get_uint64(v_key_485_, sizeof(void*)*2);
v___y_493_ = v_hash_512_;
goto v___jp_492_;
}
v___jp_492_:
{
uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v___y_493_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v___y_493_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_491_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v___x_505_ = lean_array_uget_borrowed(v_x_483_, v___x_504_);
lean_inc(v___x_505_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 2, v___x_505_);
v___x_507_ = v___x_489_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_key_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_value_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_505_);
v___x_507_ = v_reuseFailAlloc_510_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_array_uset(v_x_483_, v___x_504_, v___x_507_);
v_x_483_ = v___x_508_;
v_x_484_ = v_tail_487_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_514_, lean_object* v_source_515_, lean_object* v_target_516_){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_source_515_);
v___x_518_ = lean_nat_dec_lt(v_i_514_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_source_515_);
lean_dec(v_i_514_);
return v_target_516_;
}
else
{
lean_object* v_es_519_; lean_object* v___x_520_; lean_object* v_source_521_; lean_object* v_target_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_es_519_ = lean_array_fget(v_source_515_, v_i_514_);
v___x_520_ = lean_box(0);
v_source_521_ = lean_array_fset(v_source_515_, v_i_514_, v___x_520_);
v_target_522_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_516_, v_es_519_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_i_514_, v___x_523_);
lean_dec(v_i_514_);
v_i_514_ = v___x_524_;
v_source_515_ = v_source_521_;
v_target_516_ = v_target_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_nbuckets_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_527_ = lean_array_get_size(v_data_526_);
v___x_528_ = lean_unsigned_to_nat(2u);
v_nbuckets_529_ = lean_nat_mul(v___x_527_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_box(0);
v___x_532_ = lean_mk_array(v_nbuckets_529_, v___x_531_);
v___x_533_ = lean_array_propagate_mark(v_data_526_, v___x_532_);
v___x_534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_530_, v_data_526_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v_size_538_; lean_object* v_buckets_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_585_; 
v_size_538_ = lean_ctor_get(v_m_535_, 0);
v_buckets_539_ = lean_ctor_get(v_m_535_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_m_535_);
if (v_isSharedCheck_585_ == 0)
{
v___x_541_ = v_m_535_;
v_isShared_542_ = v_isSharedCheck_585_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_buckets_539_);
lean_inc(v_size_538_);
lean_dec(v_m_535_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_585_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; uint64_t v___y_545_; 
v___x_543_ = lean_array_get_size(v_buckets_539_);
if (lean_obj_tag(v_a_536_) == 0)
{
uint64_t v___x_583_; 
v___x_583_ = 1723ULL;
v___y_545_ = v___x_583_;
goto v___jp_544_;
}
else
{
uint64_t v_hash_584_; 
v_hash_584_ = lean_ctor_get_uint64(v_a_536_, sizeof(void*)*2);
v___y_545_ = v_hash_584_;
goto v___jp_544_;
}
v___jp_544_:
{
uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v_fold_548_; uint64_t v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; lean_object* v_bkt_557_; uint8_t v___x_558_; 
v___x_546_ = 32ULL;
v___x_547_ = lean_uint64_shift_right(v___y_545_, v___x_546_);
v_fold_548_ = lean_uint64_xor(v___y_545_, v___x_547_);
v___x_549_ = 16ULL;
v___x_550_ = lean_uint64_shift_right(v_fold_548_, v___x_549_);
v___x_551_ = lean_uint64_xor(v_fold_548_, v___x_550_);
v___x_552_ = lean_uint64_to_usize(v___x_551_);
v___x_553_ = lean_usize_of_nat(v___x_543_);
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_sub(v___x_553_, v___x_554_);
v___x_556_ = lean_usize_land(v___x_552_, v___x_555_);
v_bkt_557_ = lean_array_uget_borrowed(v_buckets_539_, v___x_556_);
v___x_558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_536_, v_bkt_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v_size_x27_560_; lean_object* v___x_561_; lean_object* v_buckets_x27_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v_size_x27_560_ = lean_nat_add(v_size_538_, v___x_559_);
lean_dec(v_size_538_);
lean_inc(v_bkt_557_);
v___x_561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_561_, 0, v_a_536_);
lean_ctor_set(v___x_561_, 1, v_b_537_);
lean_ctor_set(v___x_561_, 2, v_bkt_557_);
v_buckets_x27_562_ = lean_array_uset(v_buckets_539_, v___x_556_, v___x_561_);
v___x_563_ = lean_unsigned_to_nat(4u);
v___x_564_ = lean_nat_mul(v_size_x27_560_, v___x_563_);
v___x_565_ = lean_unsigned_to_nat(3u);
v___x_566_ = lean_nat_div(v___x_564_, v___x_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_array_get_size(v_buckets_x27_562_);
v___x_568_ = lean_nat_dec_le(v___x_566_, v___x_567_);
lean_dec(v___x_566_);
if (v___x_568_ == 0)
{
lean_object* v_val_569_; lean_object* v___x_571_; 
v_val_569_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_562_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_val_569_);
lean_ctor_set(v___x_541_, 0, v_size_x27_560_);
v___x_571_ = v___x_541_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_x27_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_val_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v___x_574_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_buckets_x27_562_);
lean_ctor_set(v___x_541_, 0, v_size_x27_560_);
v___x_574_ = v___x_541_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_size_x27_560_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_buckets_x27_562_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v___x_576_; lean_object* v_buckets_x27_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_inc(v_bkt_557_);
v___x_576_ = lean_box(0);
v_buckets_x27_577_ = lean_array_uset(v_buckets_539_, v___x_556_, v___x_576_);
v___x_578_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_536_, v_b_537_, v_bkt_557_);
v___x_579_ = lean_array_uset(v_buckets_x27_577_, v___x_556_, v___x_578_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_579_);
v___x_581_ = v___x_541_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_size_538_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_588_ = lean_mk_io_user_error(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_591_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_toAttributeImplCore_595_; lean_object* v_name_596_; uint8_t v___x_597_; 
v___x_593_ = l_Lean_attributeMapRef;
v___x_594_ = lean_st_ref_get(v___x_593_);
v_toAttributeImplCore_595_ = lean_ctor_get(v_attr_591_, 0);
v_name_596_ = lean_ctor_get(v_toAttributeImplCore_595_, 1);
lean_inc(v_name_596_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_594_, v_name_596_);
lean_dec(v___x_594_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = l_Lean_initializing();
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_name_596_);
lean_dec_ref(v_attr_591_);
v___x_599_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_st_ref_take(v___x_593_);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_601_, v_name_596_, v_attr_591_);
v___x_603_ = lean_st_ref_put(v___x_593_, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec_ref(v_attr_591_);
v___x_605_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_606_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_596_, v___x_597_);
v___x_607_ = lean_string_append(v___x_605_, v___x_606_);
lean_dec_ref(v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_609_ = lean_string_append(v___x_607_, v___x_608_);
v___x_610_ = lean_mk_io_user_error(v___x_609_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_registerBuiltinAttribute(v_attr_612_);
return v_res_614_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_615_, lean_object* v_m_616_, lean_object* v_a_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_616_, v_a_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_619_, v_m_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_m_620_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_624_, lean_object* v_m_625_, lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_625_, v_a_626_, v_b_627_);
return v___x_628_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_629_, lean_object* v_a_630_, lean_object* v_x_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_630_, v_x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_633_, v_a_634_, v_x_635_);
lean_dec(v_x_635_);
lean_dec(v_a_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_638_, lean_object* v_data_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_641_, lean_object* v_a_642_, lean_object* v_b_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_642_, v_b_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_646_, lean_object* v_i_647_, lean_object* v_source_648_, lean_object* v_target_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_647_, v_source_648_, v_target_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_652_, v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_toCold_660_; lean_object* v_currRecDepth_661_; lean_object* v_ref_662_; uint8_t v_diag_663_; uint8_t v_suppressElabErrors_664_; lean_object* v_ref_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_toCold_660_ = lean_ctor_get(v___y_657_, 0);
v_currRecDepth_661_ = lean_ctor_get(v___y_657_, 1);
v_ref_662_ = lean_ctor_get(v___y_657_, 2);
v_diag_663_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3);
v_suppressElabErrors_664_ = lean_ctor_get_uint8(v___y_657_, sizeof(void*)*3 + 1);
v_ref_665_ = l_Lean_replaceRef(v_ref_655_, v_ref_662_);
lean_inc(v_currRecDepth_661_);
lean_inc_ref(v_toCold_660_);
v___x_666_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_666_, 0, v_toCold_660_);
lean_ctor_set(v___x_666_, 1, v_currRecDepth_661_);
lean_ctor_set(v___x_666_, 2, v_ref_665_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3, v_diag_663_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3 + 1, v_suppressElabErrors_664_);
v___x_667_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_656_, v___x_666_, v___y_658_);
lean_dec_ref_known(v___x_666_, 3);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_668_, v_msg_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v_ref_668_);
return v_res_673_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; uint8_t v___y_705_; lean_object* v___x_711_; uint8_t v___x_712_; 
lean_inc(v_stx_690_);
v___x_694_ = l_Lean_Syntax_getKind(v_stx_690_);
v___x_711_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_712_ = lean_name_eq(v___x_694_, v___x_711_);
if (v___x_712_ == 0)
{
v___y_705_ = v___x_712_;
goto v___jp_704_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = l_Lean_Syntax_getArg(v_stx_690_, v___x_713_);
v___x_715_ = l_Lean_Syntax_isNone(v___x_714_);
lean_dec(v___x_714_);
v___y_705_ = v___x_715_;
goto v___jp_704_;
}
v___jp_695_:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_697_ = lean_name_eq(v___x_694_, v___x_696_);
lean_dec(v___x_694_);
if (v___x_697_ == 0)
{
if (lean_obj_tag(v_stx_690_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_701_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_690_, v___x_700_, v_a_691_, v_a_692_);
lean_dec(v_stx_690_);
return v___x_701_;
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_stx_690_);
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
v___jp_704_:
{
if (v___y_705_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(2u);
v___x_707_ = l_Lean_Syntax_getArg(v_stx_690_, v___x_706_);
v___x_708_ = l_Lean_Syntax_isNone(v___x_707_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v___x_694_);
lean_dec(v_stx_690_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_721_, lean_object* v_ref_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_722_, v_msg_723_, v___y_724_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_728_, lean_object* v_ref_729_, lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_728_, v_ref_729_, v_msg_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_ref_729_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
lean_inc(v_stx_750_);
v___x_762_ = l_Lean_Syntax_getKind(v_stx_750_);
v___x_763_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_764_ = lean_name_eq(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_766_ = lean_name_eq(v___x_762_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_768_ = lean_name_eq(v___x_762_, v___x_767_);
lean_dec(v___x_762_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_770_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_750_, v___x_769_, v_a_751_, v_a_752_);
lean_dec(v_stx_750_);
return v___x_770_;
}
else
{
goto v___jp_754_;
}
}
else
{
lean_dec(v___x_762_);
goto v___jp_754_;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
lean_dec(v___x_762_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = l_Lean_Syntax_getArg(v_stx_750_, v___x_771_);
lean_dec(v_stx_750_);
v___x_773_ = l_Lean_Syntax_isNone(v___x_772_);
if (v___x_773_ == 0)
{
if (v___x_764_ == 0)
{
lean_dec(v___x_772_);
goto v___jp_759_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_Syntax_getArg(v___x_772_, v___x_774_);
lean_dec(v___x_772_);
v___x_776_ = l_Lean_Syntax_isIdent(v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v___x_775_);
goto v___jp_759_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
else
{
lean_dec(v___x_772_);
goto v___jp_759_;
}
}
v___jp_754_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = l_Lean_Syntax_getArg(v_stx_750_, v___x_755_);
lean_dec(v_stx_750_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_783_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_791_; 
lean_inc(v_stx_787_);
v___x_791_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_787_, v_a_788_, v_a_789_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_805_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_805_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_a_792_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_794_);
v___x_796_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_787_);
v___x_797_ = l_Lean_MessageData_ofSyntax(v_stx_787_);
v___x_798_ = l_Lean_indentD(v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_787_, v___x_799_, v_a_788_, v_a_789_);
lean_dec(v_stx_787_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; 
lean_dec(v_stx_787_);
v_val_801_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_792_, 1);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v_val_801_);
v___x_803_ = v___x_794_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_stx_787_);
v_a_806_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_791_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_791_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Attribute_Builtin_getIdent(v_stx_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_844_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_828_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_843_; 
v_val_832_ = lean_ctor_get(v_a_824_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_843_ == 0)
{
v___x_834_ = v_a_824_;
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v_a_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_Syntax_getId(v_val_832_);
lean_dec(v_val_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_838_);
v___x_840_ = v___x_826_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_823_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_823_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Attribute_Builtin_getIdent(v_stx_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = l_Lean_Syntax_getId(v_a_863_);
lean_dec(v_a_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_862_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_862_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Attribute_Builtin_getId(v_stx_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_Syntax_isNone(v_optPrioStx_888_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = l_Lean_Syntax_getArg(v_optPrioStx_888_, v___x_893_);
v___x_895_ = l_Lean_Syntax_isNatLit_x3f(v___x_894_);
lean_dec(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_896_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_888_);
v___x_897_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_888_);
v___x_898_ = l_Lean_indentD(v___x_897_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_888_, v___x_899_, v_a_889_, v_a_890_);
lean_dec(v_optPrioStx_888_);
return v___x_900_;
}
else
{
lean_object* v_val_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_optPrioStx_888_);
v_val_901_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_895_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_val_901_);
lean_dec(v___x_895_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 0);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_val_901_);
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
else
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_optPrioStx_888_);
v___x_909_ = lean_unsigned_to_nat(1000u);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
lean_inc(v_stx_919_);
v___x_923_ = l_Lean_Syntax_getKind(v_stx_919_);
v___x_924_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_925_ = lean_name_eq(v___x_923_, v___x_924_);
lean_dec(v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_926_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_919_);
v___x_927_ = l_Lean_MessageData_ofSyntax(v_stx_919_);
v___x_928_ = l_Lean_indentD(v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_919_, v___x_929_, v_a_920_, v_a_921_);
lean_dec(v_stx_919_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = l_Lean_Syntax_getArg(v_stx_919_, v___x_931_);
lean_dec(v_stx_919_);
v___x_933_ = l_Lean_getAttrParamOptPrio(v___x_932_, v_a_920_, v_a_921_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Attribute_Builtin_getPrio(v_stx_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_name_950_, uint8_t v_kind_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___y_958_; 
v___x_952_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_953_ = l_Lean_MessageData_ofName(v_name_950_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
switch(v_kind_951_)
{
case 0:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_958_ = v___x_965_;
goto v___jp_957_;
}
case 1:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_958_ = v___x_966_;
goto v___jp_957_;
}
default: 
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_958_ = v___x_967_;
goto v___jp_957_;
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc_ref(v___y_958_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___y_958_);
v___x_960_ = l_Lean_MessageData_ofFormat(v___x_959_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_throwError___redArg(v_inst_948_, v_inst_949_, v___x_963_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_name_970_, lean_object* v_kind_971_){
_start:
{
uint8_t v_kind_boxed_972_; lean_object* v_res_973_; 
v_kind_boxed_972_ = lean_unbox(v_kind_971_);
v_res_973_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_968_, v_inst_969_, v_name_970_, v_kind_boxed_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_00_u03b1_977_, lean_object* v_name_978_, uint8_t v_kind_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_975_, v_inst_976_, v_name_978_, v_kind_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_00_u03b1_984_, lean_object* v_name_985_, lean_object* v_kind_986_){
_start:
{
uint8_t v_kind_boxed_987_; lean_object* v_res_988_; 
v_kind_boxed_987_ = lean_unbox(v_kind_986_);
v_res_988_ = l_Lean_throwAttrMustBeGlobal(v_m_981_, v_inst_982_, v_inst_983_, v_00_u03b1_984_, v_name_985_, v_kind_boxed_987_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_attrName_1000_, lean_object* v_declName_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1002_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1003_ = l_Lean_MessageData_ofName(v_attrName_1000_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = 0;
v___x_1008_ = l_Lean_MessageData_ofConstName(v_declName_1001_, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_throwError___redArg(v_inst_998_, v_inst_999_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_00_u03b1_1016_, lean_object* v_attrName_1017_, lean_object* v_declName_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1014_, v_inst_1015_, v_attrName_1017_, v_declName_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_attrName_1028_, lean_object* v_declName_1029_, lean_object* v_asyncPrefix_x3f_1030_){
_start:
{
lean_object* v___y_1032_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1030_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_MessageData_nil;
v___y_1032_ = v___x_1045_;
goto v___jp_1031_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1046_ = lean_ctor_get(v_asyncPrefix_x3f_1030_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v_asyncPrefix_x3f_1030_, 1);
v___x_1047_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1048_ = l_Lean_MessageData_ofName(v_val_1046_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___y_1032_ = v___x_1051_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1033_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1034_ = l_Lean_MessageData_ofName(v_attrName_1028_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = 0;
v___x_1039_ = l_Lean_MessageData_ofConstName(v_declName_1029_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___y_1032_);
v___x_1044_ = l_Lean_throwError___redArg(v_inst_1026_, v_inst_1027_, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_00_u03b1_1055_, lean_object* v_attrName_1056_, lean_object* v_declName_1057_, lean_object* v_asyncPrefix_x3f_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1053_, v_inst_1054_, v_attrName_1056_, v_declName_1057_, v_asyncPrefix_x3f_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_attrName_1074_, lean_object* v_declName_1075_, lean_object* v_givenType_1076_, lean_object* v_expectedType_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1078_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1079_ = l_Lean_MessageData_ofName(v_attrName_1074_);
lean_inc_ref(v___x_1079_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = 0;
v___x_1084_ = l_Lean_MessageData_ofConstName(v_declName_1075_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1082_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_indentExpr(v_givenType_1076_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1079_);
v___x_1093_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_indentExpr(v_expectedType_1077_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_throwError___redArg(v_inst_1072_, v_inst_1073_, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_00_u03b1_1101_, lean_object* v_attrName_1102_, lean_object* v_declName_1103_, lean_object* v_givenType_1104_, lean_object* v_expectedType_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1099_, v_inst_1100_, v_attrName_1102_, v_declName_1103_, v_givenType_1104_, v_expectedType_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1107_, uint8_t v_skipRealize_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Environment_contains(v_env_1112_, v_constName_1107_, v_skipRealize_1108_);
v___x_1114_ = lean_box(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1116_, lean_object* v_skipRealize_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_skipRealize_boxed_1120_; lean_object* v_res_1121_; 
v_skipRealize_boxed_1120_ = lean_unbox(v_skipRealize_1117_);
v_res_1121_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1116_, v_skipRealize_boxed_1120_, v___y_1118_);
lean_dec(v___y_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1122_, uint8_t v_skipRealize_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1122_, v_skipRealize_1123_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1128_, lean_object* v_skipRealize_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v_skipRealize_boxed_1133_; lean_object* v_res_1134_; 
v_skipRealize_boxed_1133_ = lean_unbox(v_skipRealize_1129_);
v_res_1134_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1128_, v_skipRealize_boxed_1133_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1135_, uint8_t v_isExporting_1136_, lean_object* v___x_1137_, lean_object* v_a_x3f_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; lean_object* v_nextMacroScope_1142_; lean_object* v_ngen_1143_; lean_object* v_auxDeclNGen_1144_; lean_object* v_traceState_1145_; lean_object* v_messages_1146_; lean_object* v_infoState_1147_; lean_object* v_snapshotTasks_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1159_; 
v___x_1140_ = lean_st_ref_take(v___y_1135_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
v_nextMacroScope_1142_ = lean_ctor_get(v___x_1140_, 1);
v_ngen_1143_ = lean_ctor_get(v___x_1140_, 2);
v_auxDeclNGen_1144_ = lean_ctor_get(v___x_1140_, 3);
v_traceState_1145_ = lean_ctor_get(v___x_1140_, 4);
v_messages_1146_ = lean_ctor_get(v___x_1140_, 6);
v_infoState_1147_ = lean_ctor_get(v___x_1140_, 7);
v_snapshotTasks_1148_ = lean_ctor_get(v___x_1140_, 8);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1140_, 5);
lean_dec(v_unused_1160_);
v___x_1150_ = v___x_1140_;
v_isShared_1151_ = v_isSharedCheck_1159_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snapshotTasks_1148_);
lean_inc(v_infoState_1147_);
lean_inc(v_messages_1146_);
lean_inc(v_traceState_1145_);
lean_inc(v_auxDeclNGen_1144_);
lean_inc(v_ngen_1143_);
lean_inc(v_nextMacroScope_1142_);
lean_inc(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1159_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = l_Lean_Environment_setExporting(v_env_1141_, v_isExporting_1136_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 5, v___x_1137_);
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_nextMacroScope_1142_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_ngen_1143_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_auxDeclNGen_1144_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_traceState_1145_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1158_, 6, v_messages_1146_);
lean_ctor_set(v_reuseFailAlloc_1158_, 7, v_infoState_1147_);
lean_ctor_set(v_reuseFailAlloc_1158_, 8, v_snapshotTasks_1148_);
v___x_1155_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_st_ref_put(v___y_1135_, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1152_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1161_, lean_object* v_isExporting_1162_, lean_object* v___x_1163_, lean_object* v_a_x3f_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_isExporting_boxed_1166_; lean_object* v_res_1167_; 
v_isExporting_boxed_1166_ = lean_unbox(v_isExporting_1162_);
v_res_1167_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1161_, v_isExporting_boxed_1166_, v___x_1163_, v_a_x3f_1164_);
lean_dec(v_a_x3f_1164_);
lean_dec(v___y_1161_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1172_, uint8_t v_isExporting_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v_env_1178_; lean_object* v___x_1179_; uint8_t v_isModule_1180_; 
v___x_1177_ = lean_st_ref_get(v___y_1175_);
v_env_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_ref(v_env_1178_);
lean_dec(v___x_1177_);
v___x_1179_ = l_Lean_Environment_header(v_env_1178_);
v_isModule_1180_ = lean_ctor_get_uint8(v___x_1179_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1179_);
if (v_isModule_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec_ref(v_env_1178_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v___x_1181_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1181_;
}
else
{
uint8_t v_isExporting_1182_; 
v_isExporting_1182_ = lean_ctor_get_uint8(v_env_1178_, sizeof(void*)*8);
lean_dec_ref(v_env_1178_);
if (v_isExporting_1173_ == 0)
{
if (v_isExporting_1182_ == 0)
{
lean_object* v___x_1233_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v___x_1233_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1233_;
}
else
{
goto v___jp_1183_;
}
}
else
{
if (v_isExporting_1182_ == 0)
{
goto v___jp_1183_;
}
else
{
lean_object* v___x_1234_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v___x_1234_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1234_;
}
}
v___jp_1183_:
{
lean_object* v___x_1184_; lean_object* v_env_1185_; lean_object* v_nextMacroScope_1186_; lean_object* v_ngen_1187_; lean_object* v_auxDeclNGen_1188_; lean_object* v_traceState_1189_; lean_object* v_messages_1190_; lean_object* v_infoState_1191_; lean_object* v_snapshotTasks_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1231_; 
v___x_1184_ = lean_st_ref_take(v___y_1175_);
v_env_1185_ = lean_ctor_get(v___x_1184_, 0);
v_nextMacroScope_1186_ = lean_ctor_get(v___x_1184_, 1);
v_ngen_1187_ = lean_ctor_get(v___x_1184_, 2);
v_auxDeclNGen_1188_ = lean_ctor_get(v___x_1184_, 3);
v_traceState_1189_ = lean_ctor_get(v___x_1184_, 4);
v_messages_1190_ = lean_ctor_get(v___x_1184_, 6);
v_infoState_1191_ = lean_ctor_get(v___x_1184_, 7);
v_snapshotTasks_1192_ = lean_ctor_get(v___x_1184_, 8);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1184_, 5);
lean_dec(v_unused_1232_);
v___x_1194_ = v___x_1184_;
v_isShared_1195_ = v_isSharedCheck_1231_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snapshotTasks_1192_);
lean_inc(v_infoState_1191_);
lean_inc(v_messages_1190_);
lean_inc(v_traceState_1189_);
lean_inc(v_auxDeclNGen_1188_);
lean_inc(v_ngen_1187_);
lean_inc(v_nextMacroScope_1186_);
lean_inc(v_env_1185_);
lean_dec(v___x_1184_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1231_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = l_Lean_Environment_setExporting(v_env_1185_, v_isExporting_1173_);
v___x_1197_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 5, v___x_1197_);
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_nextMacroScope_1186_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_ngen_1187_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_auxDeclNGen_1188_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_traceState_1189_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_messages_1190_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v_infoState_1191_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_snapshotTasks_1192_);
v___x_1199_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v_r_1201_; 
v___x_1200_ = lean_st_ref_put(v___y_1175_, v___x_1199_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v_r_1201_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
if (lean_obj_tag(v_r_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1218_; 
v_a_1202_ = lean_ctor_get(v_r_1201_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_r_1201_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1204_ = v_r_1201_;
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v_r_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
lean_inc(v_a_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 1);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v___x_1208_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1175_, v_isExporting_1182_, v___x_1197_, v___x_1207_);
lean_dec_ref(v___x_1207_);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1208_, 0);
lean_dec(v_unused_1216_);
v___x_1210_ = v___x_1208_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v___x_1208_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v_a_1202_);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1202_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1219_ = lean_ctor_get(v_r_1201_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v_r_1201_, 1);
v___x_1220_ = lean_box(0);
v___x_1221_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1175_, v_isExporting_1182_, v___x_1197_, v___x_1220_);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1229_);
v___x_1223_ = v___x_1221_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v___x_1221_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 1);
lean_ctor_set(v___x_1223_, 0, v_a_1219_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1219_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1235_, lean_object* v_isExporting_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_isExporting_boxed_1240_; lean_object* v_res_1241_; 
v_isExporting_boxed_1240_ = lean_unbox(v_isExporting_1236_);
v_res_1241_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1235_, v_isExporting_boxed_1240_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1242_, lean_object* v_x_1243_, uint8_t v_isExporting_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1243_, v_isExporting_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_x_1250_, lean_object* v_isExporting_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
uint8_t v_isExporting_boxed_1255_; lean_object* v_res_1256_; 
v_isExporting_boxed_1255_ = lean_unbox(v_isExporting_1251_);
v_res_1256_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1249_, v_x_1250_, v_isExporting_boxed_1255_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1256_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1257_, lean_object* v_opt_1258_){
_start:
{
lean_object* v_name_1259_; lean_object* v_defValue_1260_; lean_object* v_map_1261_; lean_object* v___x_1262_; 
v_name_1259_ = lean_ctor_get(v_opt_1258_, 0);
v_defValue_1260_ = lean_ctor_get(v_opt_1258_, 1);
v_map_1261_ = lean_ctor_get(v_opts_1257_, 0);
v___x_1262_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1261_, v_name_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_unbox(v_defValue_1260_);
return v___x_1263_;
}
else
{
lean_object* v_val_1264_; 
v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1262_, 1);
if (lean_obj_tag(v_val_1264_) == 1)
{
uint8_t v_v_1265_; 
v_v_1265_ = lean_ctor_get_uint8(v_val_1264_, 0);
lean_dec_ref_known(v_val_1264_, 0);
return v_v_1265_;
}
else
{
uint8_t v___x_1266_; 
lean_dec(v_val_1264_);
v___x_1266_ = lean_unbox(v_defValue_1260_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1267_, lean_object* v_opt_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1267_, v_opt_1268_);
lean_dec_ref(v_opt_1268_);
lean_dec_ref(v_opts_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1278_, uint8_t v___y_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 1)
{
lean_object* v_pre_1281_; 
v_pre_1281_ = lean_ctor_get(v_x_1280_, 0);
switch(lean_obj_tag(v_pre_1281_))
{
case 1:
{
lean_object* v_pre_1282_; 
v_pre_1282_ = lean_ctor_get(v_pre_1281_, 0);
switch(lean_obj_tag(v_pre_1282_))
{
case 0:
{
lean_object* v_str_1283_; lean_object* v_str_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_str_1283_ = lean_ctor_get(v_x_1280_, 1);
v_str_1284_ = lean_ctor_get(v_pre_1281_, 1);
v___x_1285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1286_ = lean_string_dec_eq(v_str_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1288_ = lean_string_dec_eq(v_str_1284_, v___x_1287_);
if (v___x_1288_ == 0)
{
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1290_ = lean_string_dec_eq(v_str_1283_, v___x_1289_);
if (v___x_1290_ == 0)
{
return v___x_1290_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
}
else
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1292_ = lean_string_dec_eq(v_str_1283_, v___x_1291_);
if (v___x_1292_ == 0)
{
return v___x_1292_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
}
case 1:
{
lean_object* v_pre_1293_; 
v_pre_1293_ = lean_ctor_get(v_pre_1282_, 0);
if (lean_obj_tag(v_pre_1293_) == 0)
{
lean_object* v_str_1294_; lean_object* v_str_1295_; lean_object* v_str_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_str_1294_ = lean_ctor_get(v_x_1280_, 1);
v_str_1295_ = lean_ctor_get(v_pre_1281_, 1);
v_str_1296_ = lean_ctor_get(v_pre_1282_, 1);
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1298_ = lean_string_dec_eq(v_str_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1300_ = lean_string_dec_eq(v_str_1295_, v___x_1299_);
if (v___x_1300_ == 0)
{
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1302_ = lean_string_dec_eq(v_str_1294_, v___x_1301_);
if (v___x_1302_ == 0)
{
return v___x_1302_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
}
}
else
{
return v___y_1279_;
}
}
default: 
{
return v___y_1279_;
}
}
}
case 0:
{
lean_object* v_str_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_str_1303_ = lean_ctor_get(v_x_1280_, 1);
v___x_1304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1305_ = lean_string_dec_eq(v_str_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
return v___x_1305_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
default: 
{
return v___y_1279_;
}
}
}
else
{
return v___y_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1306_, lean_object* v___y_1307_, lean_object* v_x_1308_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1309_; uint8_t v___y_5064__boxed_1310_; uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_suppressElabErrors_boxed_1309_ = lean_unbox(v_suppressElabErrors_1306_);
v___y_5064__boxed_1310_ = lean_unbox(v___y_1307_);
v_res_1311_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1309_, v___y_5064__boxed_1310_, v_x_1308_);
lean_dec(v_x_1308_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1313_, lean_object* v_msgData_1314_, uint8_t v_severity_1315_, uint8_t v_isSilent_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v_currNamespace_1328_; lean_object* v_openDecls_1329_; lean_object* v___y_1330_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; uint8_t v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; uint8_t v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1403_; uint8_t v___y_1404_; uint8_t v___x_1409_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; uint8_t v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1421_; uint8_t v___x_1439_; 
v___x_1409_ = 2;
v___x_1439_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1315_, v___x_1409_);
if (v___x_1439_ == 0)
{
v___y_1421_ = v___x_1439_;
goto v___jp_1420_;
}
else
{
uint8_t v___x_1440_; 
lean_inc_ref(v_msgData_1314_);
v___x_1440_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1314_);
v___y_1421_ = v___x_1440_;
goto v___jp_1420_;
}
v___jp_1320_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_env_1335_; lean_object* v_nextMacroScope_1336_; lean_object* v_ngen_1337_; lean_object* v_auxDeclNGen_1338_; lean_object* v_traceState_1339_; lean_object* v_cache_1340_; lean_object* v_messages_1341_; lean_object* v_infoState_1342_; lean_object* v_snapshotTasks_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1354_; 
lean_inc(v_openDecls_1329_);
lean_inc(v_currNamespace_1328_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_currNamespace_1328_);
lean_ctor_set(v___x_1331_, 1, v_openDecls_1329_);
v___x_1332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___y_1322_);
lean_inc_ref(v___y_1323_);
lean_inc_ref(v___y_1326_);
v___x_1333_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1333_, 0, v___y_1326_);
lean_ctor_set(v___x_1333_, 1, v___y_1325_);
lean_ctor_set(v___x_1333_, 2, v___y_1327_);
lean_ctor_set(v___x_1333_, 3, v___y_1323_);
lean_ctor_set(v___x_1333_, 4, v___x_1332_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*5, v___y_1324_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*5 + 1, v___y_1321_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*5 + 2, v_isSilent_1316_);
v___x_1334_ = lean_st_ref_take(v___y_1330_);
v_env_1335_ = lean_ctor_get(v___x_1334_, 0);
v_nextMacroScope_1336_ = lean_ctor_get(v___x_1334_, 1);
v_ngen_1337_ = lean_ctor_get(v___x_1334_, 2);
v_auxDeclNGen_1338_ = lean_ctor_get(v___x_1334_, 3);
v_traceState_1339_ = lean_ctor_get(v___x_1334_, 4);
v_cache_1340_ = lean_ctor_get(v___x_1334_, 5);
v_messages_1341_ = lean_ctor_get(v___x_1334_, 6);
v_infoState_1342_ = lean_ctor_get(v___x_1334_, 7);
v_snapshotTasks_1343_ = lean_ctor_get(v___x_1334_, 8);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1345_ = v___x_1334_;
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snapshotTasks_1343_);
lean_inc(v_infoState_1342_);
lean_inc(v_messages_1341_);
lean_inc(v_cache_1340_);
lean_inc(v_traceState_1339_);
lean_inc(v_auxDeclNGen_1338_);
lean_inc(v_ngen_1337_);
lean_inc(v_nextMacroScope_1336_);
lean_inc(v_env_1335_);
lean_dec(v___x_1334_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = l_Lean_MessageLog_add(v___x_1333_, v_messages_1341_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 6, v___x_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_env_1335_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_nextMacroScope_1336_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_ngen_1337_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_auxDeclNGen_1338_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v_traceState_1339_);
lean_ctor_set(v_reuseFailAlloc_1353_, 5, v_cache_1340_);
lean_ctor_set(v_reuseFailAlloc_1353_, 6, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1353_, 7, v_infoState_1342_);
lean_ctor_set(v_reuseFailAlloc_1353_, 8, v_snapshotTasks_1343_);
v___x_1350_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_st_ref_put(v___y_1330_, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1347_);
return v___x_1352_;
}
}
}
v___jp_1355_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1381_; 
v___x_1366_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1314_);
v___x_1367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1366_, v___y_1317_, v___y_1318_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc_ref_n(v___y_1361_, 2);
v___x_1372_ = l_Lean_FileMap_toPosition(v___y_1361_, v___y_1359_);
lean_dec(v___y_1359_);
v___x_1373_ = l_Lean_FileMap_toPosition(v___y_1361_, v___y_1365_);
lean_dec(v___y_1365_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1362_ == 0)
{
lean_del_object(v___x_1370_);
lean_dec_ref(v___y_1356_);
v___y_1321_ = v___y_1360_;
v___y_1322_ = v_a_1368_;
v___y_1323_ = v___x_1375_;
v___y_1324_ = v___y_1364_;
v___y_1325_ = v___x_1372_;
v___y_1326_ = v___y_1363_;
v___y_1327_ = v___x_1374_;
v_currNamespace_1328_ = v___y_1357_;
v_openDecls_1329_ = v___y_1358_;
v___y_1330_ = v___y_1318_;
goto v___jp_1320_;
}
else
{
uint8_t v___x_1376_; 
lean_inc(v_a_1368_);
v___x_1376_ = l_Lean_MessageData_hasTag(v___y_1356_, v_a_1368_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1374_, 1);
lean_dec_ref(v___x_1372_);
lean_dec(v_a_1368_);
v___x_1377_ = lean_box(0);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1377_);
v___x_1379_ = v___x_1370_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_del_object(v___x_1370_);
v___y_1321_ = v___y_1360_;
v___y_1322_ = v_a_1368_;
v___y_1323_ = v___x_1375_;
v___y_1324_ = v___y_1364_;
v___y_1325_ = v___x_1372_;
v___y_1326_ = v___y_1363_;
v___y_1327_ = v___x_1374_;
v_currNamespace_1328_ = v___y_1357_;
v_openDecls_1329_ = v___y_1358_;
v___y_1330_ = v___y_1318_;
goto v___jp_1320_;
}
}
}
}
v___jp_1382_:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Syntax_getTailPos_x3f(v___y_1391_, v___y_1389_);
lean_dec(v___y_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_inc(v___y_1392_);
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___y_1392_;
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1390_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1392_;
goto v___jp_1355_;
}
else
{
lean_object* v_val_1394_; 
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___y_1356_ = v___y_1383_;
v___y_1357_ = v___y_1384_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v___y_1392_;
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1386_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1390_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v_val_1394_;
goto v___jp_1355_;
}
}
v___jp_1395_:
{
lean_object* v_ref_1405_; lean_object* v___x_1406_; 
v_ref_1405_ = l_Lean_replaceRef(v_ref_1313_, v___y_1400_);
v___x_1406_ = l_Lean_Syntax_getPos_x3f(v_ref_1405_, v___y_1403_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___y_1397_;
v___y_1385_ = v___y_1398_;
v___y_1386_ = v___y_1399_;
v___y_1387_ = v___y_1404_;
v___y_1388_ = v___y_1401_;
v___y_1389_ = v___y_1403_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v_ref_1405_;
v___y_1392_ = v___x_1407_;
goto v___jp_1382_;
}
else
{
lean_object* v_val_1408_; 
v_val_1408_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1406_, 1);
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___y_1397_;
v___y_1385_ = v___y_1398_;
v___y_1386_ = v___y_1399_;
v___y_1387_ = v___y_1404_;
v___y_1388_ = v___y_1401_;
v___y_1389_ = v___y_1403_;
v___y_1390_ = v___y_1402_;
v___y_1391_ = v_ref_1405_;
v___y_1392_ = v_val_1408_;
goto v___jp_1382_;
}
}
v___jp_1410_:
{
if (v___y_1419_ == 0)
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v___y_1414_;
v___y_1398_ = v___y_1415_;
v___y_1399_ = v___y_1411_;
v___y_1400_ = v___y_1416_;
v___y_1401_ = v___y_1417_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v___y_1418_;
v___y_1404_ = v_severity_1315_;
goto v___jp_1395_;
}
else
{
v___y_1396_ = v___y_1412_;
v___y_1397_ = v___y_1414_;
v___y_1398_ = v___y_1415_;
v___y_1399_ = v___y_1411_;
v___y_1400_ = v___y_1416_;
v___y_1401_ = v___y_1417_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v___y_1418_;
v___y_1404_ = v___x_1409_;
goto v___jp_1395_;
}
}
v___jp_1420_:
{
if (v___y_1421_ == 0)
{
lean_object* v_toCold_1422_; lean_object* v_ref_1423_; uint8_t v_suppressElabErrors_1424_; lean_object* v_fileName_1425_; lean_object* v_fileMap_1426_; lean_object* v_options_1427_; lean_object* v_currNamespace_1428_; lean_object* v_openDecls_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; uint8_t v___x_1433_; uint8_t v___x_1434_; 
v_toCold_1422_ = lean_ctor_get(v___y_1317_, 0);
v_ref_1423_ = lean_ctor_get(v___y_1317_, 2);
v_suppressElabErrors_1424_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 1);
v_fileName_1425_ = lean_ctor_get(v_toCold_1422_, 0);
v_fileMap_1426_ = lean_ctor_get(v_toCold_1422_, 1);
v_options_1427_ = lean_ctor_get(v_toCold_1422_, 2);
v_currNamespace_1428_ = lean_ctor_get(v_toCold_1422_, 4);
v_openDecls_1429_ = lean_ctor_get(v_toCold_1422_, 5);
v___x_1430_ = lean_box(v_suppressElabErrors_1424_);
v___x_1431_ = lean_box(v___y_1421_);
v___f_1432_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1432_, 0, v___x_1430_);
lean_closure_set(v___f_1432_, 1, v___x_1431_);
v___x_1433_ = 1;
v___x_1434_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1315_, v___x_1433_);
if (v___x_1434_ == 0)
{
v___y_1411_ = v_fileMap_1426_;
v___y_1412_ = v___f_1432_;
v___y_1413_ = v_fileName_1425_;
v___y_1414_ = v_currNamespace_1428_;
v___y_1415_ = v_openDecls_1429_;
v___y_1416_ = v_ref_1423_;
v___y_1417_ = v_suppressElabErrors_1424_;
v___y_1418_ = v___y_1421_;
v___y_1419_ = v___x_1434_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = l_Lean_warningAsError;
v___x_1436_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1427_, v___x_1435_);
v___y_1411_ = v_fileMap_1426_;
v___y_1412_ = v___f_1432_;
v___y_1413_ = v_fileName_1425_;
v___y_1414_ = v_currNamespace_1428_;
v___y_1415_ = v_openDecls_1429_;
v___y_1416_ = v_ref_1423_;
v___y_1417_ = v_suppressElabErrors_1424_;
v___y_1418_ = v___y_1421_;
v___y_1419_ = v___x_1436_;
goto v___jp_1410_;
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_msgData_1314_);
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1441_, lean_object* v_msgData_1442_, lean_object* v_severity_1443_, lean_object* v_isSilent_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v_severity_boxed_1448_; uint8_t v_isSilent_boxed_1449_; lean_object* v_res_1450_; 
v_severity_boxed_1448_ = lean_unbox(v_severity_1443_);
v_isSilent_boxed_1449_ = lean_unbox(v_isSilent_1444_);
v_res_1450_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1441_, v_msgData_1442_, v_severity_boxed_1448_, v_isSilent_boxed_1449_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v_ref_1441_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1451_, uint8_t v_severity_1452_, uint8_t v_isSilent_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_ref_1457_; lean_object* v___x_1458_; 
v_ref_1457_ = lean_ctor_get(v___y_1454_, 2);
v___x_1458_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1457_, v_msgData_1451_, v_severity_1452_, v_isSilent_1453_, v___y_1454_, v___y_1455_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1459_, lean_object* v_severity_1460_, lean_object* v_isSilent_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v_severity_boxed_1465_; uint8_t v_isSilent_boxed_1466_; lean_object* v_res_1467_; 
v_severity_boxed_1465_ = lean_unbox(v_severity_1460_);
v_isSilent_boxed_1466_ = lean_unbox(v_isSilent_1461_);
v_res_1467_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1459_, v_severity_boxed_1465_, v_isSilent_boxed_1466_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = 1;
v___x_1473_ = 0;
v___x_1474_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1468_, v___x_1472_, v___x_1473_, v___y_1469_, v___y_1470_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_toCold_1483_; lean_object* v_options_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_toCold_1483_ = lean_ctor_get(v___y_1481_, 0);
v_options_1484_ = lean_ctor_get(v_toCold_1483_, 2);
v___x_1485_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1484_, v_opt_1480_);
v___x_1486_ = lean_box(v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1488_, v___y_1489_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v_opt_1488_);
return v_res_1491_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v_env_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1525_; 
v___x_1502_ = lean_st_ref_get(v___y_1500_);
v_env_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1505_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1504_, v___y_1499_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1525_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1525_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint8_t v_isExporting_1515_; 
v_isExporting_1515_ = lean_ctor_get_uint8(v_env_1503_, sizeof(void*)*8);
lean_dec_ref(v_env_1503_);
if (v_isExporting_1515_ == 0)
{
lean_dec(v_a_1506_);
lean_dec(v_id_1498_);
goto v___jp_1510_;
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = l_Lean_isPrivateName(v_id_1498_);
if (v___x_1516_ == 0)
{
lean_dec(v_a_1506_);
lean_dec(v_id_1498_);
goto v___jp_1510_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_unbox(v_a_1506_);
lean_dec(v_a_1506_);
if (v___x_1517_ == 0)
{
lean_dec(v_id_1498_);
goto v___jp_1510_;
}
else
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_del_object(v___x_1508_);
v___x_1518_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1519_ = 0;
v___x_1520_ = l_Lean_MessageData_ofConstName(v_id_1498_, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1518_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1523_, v___y_1499_, v___y_1500_);
return v___x_1524_;
}
}
}
v___jp_1510_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1534_, uint8_t v_isModule_1535_, lean_object* v_attrName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
lean_inc(v_declName_1534_);
v___x_1540_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1534_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref_known(v___x_1540_, 1);
lean_inc(v_declName_1534_);
v___x_1541_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1534_, v_isModule_1535_, v___y_1538_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1562_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1562_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_unbox(v_a_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_del_object(v___x_1544_);
v___x_1547_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1548_ = l_Lean_MessageData_ofName(v_attrName_1536_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
v___x_1553_ = l_Lean_MessageData_ofConstName(v_declName_1534_, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1551_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1556_, v___y_1537_, v___y_1538_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
lean_dec(v_a_1542_);
lean_dec(v_attrName_1536_);
lean_dec(v_declName_1534_);
v___x_1558_ = lean_box(0);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1558_);
v___x_1560_ = v___x_1544_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_dec(v_attrName_1536_);
lean_dec(v_declName_1534_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1563_, lean_object* v_isModule_1564_, lean_object* v_attrName_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_isModule_boxed_1569_; lean_object* v_res_1570_; 
v_isModule_boxed_1569_ = lean_unbox(v_isModule_1564_);
v_res_1570_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1563_, v_isModule_boxed_1569_, v_attrName_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1571_, lean_object* v_declName_1572_, uint8_t v_attrKind_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_env_1581_; lean_object* v___x_1582_; uint8_t v_isModule_1583_; 
v___x_1577_ = lean_st_ref_get(v_a_1575_);
v_env_1581_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_env_1581_);
lean_dec(v___x_1577_);
v___x_1582_ = l_Lean_Environment_header(v_env_1581_);
lean_dec_ref(v_env_1581_);
v_isModule_1583_ = lean_ctor_get_uint8(v___x_1582_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1582_);
if (v_isModule_1583_ == 0)
{
lean_dec(v_declName_1572_);
lean_dec(v_attrName_1571_);
goto v___jp_1578_;
}
else
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = 1;
v___x_1585_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1573_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(v_isModule_1583_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1587_, 0, v_declName_1572_);
lean_closure_set(v___f_1587_, 1, v___x_1586_);
lean_closure_set(v___f_1587_, 2, v_attrName_1571_);
v___x_1588_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1587_, v_isModule_1583_, v_a_1574_, v_a_1575_);
return v___x_1588_;
}
else
{
lean_dec(v_declName_1572_);
lean_dec(v_attrName_1571_);
goto v___jp_1578_;
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1589_, lean_object* v_declName_1590_, lean_object* v_attrKind_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
uint8_t v_attrKind_boxed_1595_; lean_object* v_res_1596_; 
v_attrKind_boxed_1595_ = lean_unbox(v_attrKind_1591_);
v_res_1596_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1589_, v_declName_1590_, v_attrKind_boxed_1595_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1597_, v___y_1598_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_opt_1602_);
return v_res_1606_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1610_, lean_object* v_declName_1611_, uint8_t v_attrKind_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v_env_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v_isModule_1620_; 
v___x_1616_ = lean_st_ref_get(v_a_1614_);
v_env_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc_ref(v_env_1617_);
lean_dec(v___x_1616_);
v___x_1618_ = lean_st_ref_get(v_a_1614_);
v___x_1619_ = l_Lean_Environment_header(v_env_1617_);
lean_dec_ref(v_env_1617_);
v_isModule_1620_ = lean_ctor_get_uint8(v___x_1619_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1619_);
if (v_isModule_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v___x_1618_);
v___x_1621_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1610_, v_declName_1611_, v_attrKind_1612_, v_a_1613_, v_a_1614_);
return v___x_1621_;
}
else
{
lean_object* v_env_1622_; uint8_t v___x_1623_; 
v_env_1622_ = lean_ctor_get(v___x_1618_, 0);
lean_inc_ref(v_env_1622_);
lean_dec(v___x_1618_);
lean_inc(v_declName_1611_);
v___x_1623_ = l_Lean_isMarkedMeta(v_env_1622_, v_declName_1611_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1624_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1625_ = l_Lean_MessageData_ofName(v_attrName_1610_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = l_Lean_MessageData_ofConstName(v_declName_1611_, v___x_1623_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1632_, v_a_1613_, v_a_1614_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1610_, v_declName_1611_, v_attrKind_1612_, v_a_1613_, v_a_1614_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1635_, lean_object* v_declName_1636_, lean_object* v_attrKind_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
uint8_t v_attrKind_boxed_1641_; lean_object* v_res_1642_; 
v_attrKind_boxed_1641_ = lean_unbox(v_attrKind_1637_);
v_res_1642_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1635_, v_declName_1636_, v_attrKind_boxed_1641_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1651_, v___y_1652_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v_x_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1655_, lean_object* v_x_1656_){
_start:
{
lean_inc(v_s_1655_);
return v_s_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec(v_s_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1667_, v_x_1668_);
lean_dec(v_x_1668_);
lean_dec_ref(v_x_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_box(0);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1672_);
lean_dec(v_x_1672_);
return v_res_1673_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___f_1679_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1680_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1681_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1682_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1685_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v___x_1683_);
lean_ctor_set(v___x_1685_, 2, v___f_1682_);
lean_ctor_set(v___x_1685_, 3, v___f_1681_);
lean_ctor_set(v___x_1685_, 4, v___f_1680_);
lean_ctor_set(v___x_1685_, 5, v___f_1679_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1687_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_registerTagAttribute___lam__0(v_x_1694_);
lean_dec(v_x_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
return v_x_1697_;
}
else
{
lean_object* v_head_1699_; lean_object* v_tail_1700_; uint8_t v___x_1701_; 
v_head_1699_ = lean_ctor_get(v_x_1698_, 0);
lean_inc(v_head_1699_);
v_tail_1700_ = lean_ctor_get(v_x_1698_, 1);
lean_inc(v_tail_1700_);
lean_dec_ref_known(v_x_1698_, 2);
v___x_1701_ = l_Lean_NameSet_contains(v_newState_1696_, v_head_1699_);
if (v___x_1701_ == 0)
{
lean_dec(v_head_1699_);
v_x_1698_ = v_tail_1700_;
goto _start;
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_NameSet_insert(v_x_1697_, v_head_1699_);
v_x_1697_ = v___x_1703_;
v_x_1698_ = v_tail_1700_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1705_, v_x_1706_, v_x_1707_);
lean_dec(v_newState_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1709_, lean_object* v_newState_1710_, lean_object* v_newConsts_1711_, lean_object* v_s_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1710_, v_s_1712_, v_newConsts_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1714_, lean_object* v_newState_1715_, lean_object* v_newConsts_1716_, lean_object* v_s_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_registerTagAttribute___lam__1(v_x_1714_, v_newState_1715_, v_newConsts_1716_, v_s_1717_);
lean_dec(v_newState_1715_);
lean_dec(v_x_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1731_){
_start:
{
lean_object* v___x_1732_; lean_object* v___y_1734_; 
v___x_1732_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1731_) == 0)
{
lean_object* v_size_1738_; 
v_size_1738_ = lean_ctor_get(v_s_1731_, 0);
lean_inc(v_size_1738_);
lean_dec_ref_known(v_s_1731_, 5);
v___y_1734_ = v_size_1738_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v___y_1734_ = v___x_1739_;
goto v___jp_1733_;
}
v___jp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = l_Nat_reprFast(v___y_1734_);
v___x_1736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1732_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1740_, lean_object* v_pivot_1741_, lean_object* v_as_1742_, lean_object* v_i_1743_, lean_object* v_k_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_lt(v_k_1744_, v_hi_1740_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_k_1744_);
v___x_1746_ = lean_array_fswap(v_as_1742_, v_i_1743_, v_hi_1740_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_i_1743_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = lean_array_fget_borrowed(v_as_1742_, v_k_1744_);
v___x_1749_ = l_Lean_Name_quickLt(v___x_1748_, v_pivot_1741_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_k_1744_, v___x_1750_);
lean_dec(v_k_1744_);
v_k_1744_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1753_ = lean_array_fswap(v_as_1742_, v_i_1743_, v_k_1744_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_nat_add(v_i_1743_, v___x_1754_);
lean_dec(v_i_1743_);
v___x_1756_ = lean_nat_add(v_k_1744_, v___x_1754_);
lean_dec(v_k_1744_);
v_as_1742_ = v___x_1753_;
v_i_1743_ = v___x_1755_;
v_k_1744_ = v___x_1756_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1758_, lean_object* v_pivot_1759_, lean_object* v_as_1760_, lean_object* v_i_1761_, lean_object* v_k_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1758_, v_pivot_1759_, v_as_1760_, v_i_1761_, v_k_1762_);
lean_dec(v_pivot_1759_);
lean_dec(v_hi_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1764_, lean_object* v_as_1765_, lean_object* v_lo_1766_, lean_object* v_hi_1767_){
_start:
{
lean_object* v___y_1769_; uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_lt(v_lo_1766_, v_hi_1767_);
if (v___x_1779_ == 0)
{
lean_dec(v_lo_1766_);
return v_as_1765_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_mid_1782_; lean_object* v___y_1784_; lean_object* v___y_1790_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1780_ = lean_nat_add(v_lo_1766_, v_hi_1767_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v_mid_1782_ = lean_nat_shiftr(v___x_1780_, v___x_1781_);
lean_dec(v___x_1780_);
v___x_1795_ = lean_array_fget_borrowed(v_as_1765_, v_mid_1782_);
v___x_1796_ = lean_array_fget_borrowed(v_as_1765_, v_lo_1766_);
v___x_1797_ = l_Lean_Name_quickLt(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
v___y_1790_ = v_as_1765_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_array_fswap(v_as_1765_, v_lo_1766_, v_mid_1782_);
v___y_1790_ = v___x_1798_;
goto v___jp_1789_;
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = lean_array_fget_borrowed(v___y_1784_, v_mid_1782_);
v___x_1786_ = lean_array_fget_borrowed(v___y_1784_, v_hi_1767_);
v___x_1787_ = l_Lean_Name_quickLt(v___x_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec(v_mid_1782_);
v___y_1769_ = v___y_1784_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_array_fswap(v___y_1784_, v_mid_1782_, v_hi_1767_);
lean_dec(v_mid_1782_);
v___y_1769_ = v___x_1788_;
goto v___jp_1768_;
}
}
v___jp_1789_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = lean_array_fget_borrowed(v___y_1790_, v_hi_1767_);
v___x_1792_ = lean_array_fget_borrowed(v___y_1790_, v_lo_1766_);
v___x_1793_ = l_Lean_Name_quickLt(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
v___y_1784_ = v___y_1790_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_array_fswap(v___y_1790_, v_lo_1766_, v_hi_1767_);
v___y_1784_ = v___x_1794_;
goto v___jp_1783_;
}
}
}
v___jp_1768_:
{
lean_object* v_pivot_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; uint8_t v___x_1774_; 
v_pivot_1770_ = lean_array_fget(v___y_1769_, v_hi_1767_);
lean_inc_n(v_lo_1766_, 2);
v___x_1771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1767_, v_pivot_1770_, v___y_1769_, v_lo_1766_, v_lo_1766_);
lean_dec(v_pivot_1770_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v___x_1771_);
v___x_1774_ = lean_nat_dec_le(v_hi_1767_, v_fst_1772_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1764_, v_snd_1773_, v_lo_1766_, v_fst_1772_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_fst_1772_, v___x_1776_);
lean_dec(v_fst_1772_);
v_as_1765_ = v___x_1775_;
v_lo_1766_ = v___x_1777_;
goto _start;
}
else
{
lean_dec(v_fst_1772_);
lean_dec(v_lo_1766_);
return v_snd_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1799_, lean_object* v_as_1800_, lean_object* v_lo_1801_, lean_object* v_hi_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1799_, v_as_1800_, v_lo_1801_, v_hi_1802_);
lean_dec(v_hi_1802_);
lean_dec(v_n_1799_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1804_, lean_object* v_as_1805_, size_t v_i_1806_, size_t v_stop_1807_, lean_object* v_b_1808_){
_start:
{
lean_object* v___y_1810_; uint8_t v___x_1814_; 
v___x_1814_ = lean_usize_dec_eq(v_i_1806_, v_stop_1807_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = lean_array_uget_borrowed(v_as_1805_, v_i_1806_);
v___x_1816_ = 1;
lean_inc_ref(v_env_1804_);
v___x_1817_ = l_Lean_Environment_setExporting(v_env_1804_, v___x_1816_);
lean_inc(v___x_1815_);
v___x_1818_ = l_Lean_Environment_contains(v___x_1817_, v___x_1815_, v___x_1814_);
if (v___x_1818_ == 0)
{
v___y_1810_ = v_b_1808_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1819_; 
lean_inc(v___x_1815_);
v___x_1819_ = lean_array_push(v_b_1808_, v___x_1815_);
v___y_1810_ = v___x_1819_;
goto v___jp_1809_;
}
}
else
{
lean_dec_ref(v_env_1804_);
return v_b_1808_;
}
v___jp_1809_:
{
size_t v___x_1811_; size_t v___x_1812_; 
v___x_1811_ = ((size_t)1ULL);
v___x_1812_ = lean_usize_add(v_i_1806_, v___x_1811_);
v_i_1806_ = v___x_1812_;
v_b_1808_ = v___y_1810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1820_, lean_object* v_as_1821_, lean_object* v_i_1822_, lean_object* v_stop_1823_, lean_object* v_b_1824_){
_start:
{
size_t v_i_boxed_1825_; size_t v_stop_boxed_1826_; lean_object* v_res_1827_; 
v_i_boxed_1825_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_stop_boxed_1826_ = lean_unbox_usize(v_stop_1823_);
lean_dec(v_stop_1823_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1820_, v_as_1821_, v_i_boxed_1825_, v_stop_boxed_1826_, v_b_1824_);
lean_dec_ref(v_as_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1829_) == 0)
{
lean_object* v_k_1830_; lean_object* v_l_1831_; lean_object* v_r_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_k_1830_ = lean_ctor_get(v_x_1829_, 1);
lean_inc(v_k_1830_);
v_l_1831_ = lean_ctor_get(v_x_1829_, 3);
lean_inc(v_l_1831_);
v_r_1832_ = lean_ctor_get(v_x_1829_, 4);
lean_inc(v_r_1832_);
lean_dec_ref_known(v_x_1829_, 5);
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1828_, v_l_1831_);
v___x_1834_ = lean_array_push(v___x_1833_, v_k_1830_);
v_init_1828_ = v___x_1834_;
v_x_1829_ = v_r_1832_;
goto _start;
}
else
{
return v_init_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1836_, lean_object* v_es_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___y_1841_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; uint8_t v___x_1861_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1839_, v_es_1837_);
v___x_1856_ = lean_array_get_size(v___x_1855_);
v___x_1861_ = lean_nat_dec_eq(v___x_1856_, v___x_1838_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___y_1865_; uint8_t v___x_1867_; 
v___x_1862_ = lean_unsigned_to_nat(1u);
v___x_1863_ = lean_nat_sub(v___x_1856_, v___x_1862_);
v___x_1867_ = lean_nat_dec_le(v___x_1838_, v___x_1863_);
if (v___x_1867_ == 0)
{
lean_inc(v___x_1863_);
v___y_1865_ = v___x_1863_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___x_1838_;
goto v___jp_1864_;
}
v___jp_1864_:
{
uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_le(v___y_1865_, v___x_1863_);
if (v___x_1866_ == 0)
{
lean_dec(v___x_1863_);
lean_inc(v___y_1865_);
v___y_1858_ = v___y_1865_;
v___y_1859_ = v___y_1865_;
goto v___jp_1857_;
}
else
{
v___y_1858_ = v___y_1865_;
v___y_1859_ = v___x_1863_;
goto v___jp_1857_;
}
}
}
else
{
v___y_1841_ = v___x_1855_;
goto v___jp_1840_;
}
v___jp_1840_:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_array_get_size(v___y_1841_);
v___x_1843_ = lean_nat_dec_lt(v___x_1838_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref(v_env_1836_);
v___x_1844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
lean_ctor_set(v___x_1844_, 1, v___x_1839_);
lean_ctor_set(v___x_1844_, 2, v___y_1841_);
return v___x_1844_;
}
else
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_le(v___x_1842_, v___x_1842_);
if (v___x_1845_ == 0)
{
if (v___x_1843_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v_env_1836_);
v___x_1846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1839_);
lean_ctor_set(v___x_1846_, 1, v___x_1839_);
lean_ctor_set(v___x_1846_, 2, v___y_1841_);
return v___x_1846_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_of_nat(v___x_1842_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1836_, v___y_1841_, v___x_1847_, v___x_1848_, v___x_1839_);
lean_inc_ref(v___x_1849_);
v___x_1850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
lean_ctor_set(v___x_1850_, 2, v___y_1841_);
return v___x_1850_;
}
}
else
{
size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1842_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1836_, v___y_1841_, v___x_1851_, v___x_1852_, v___x_1839_);
lean_inc_ref(v___x_1853_);
v___x_1854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
lean_ctor_set(v___x_1854_, 2, v___y_1841_);
return v___x_1854_;
}
}
}
v___jp_1857_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1856_, v___x_1855_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
v___y_1841_ = v___x_1860_;
goto v___jp_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1868_, lean_object* v_decl_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1873_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1874_ = l_Lean_MessageData_ofName(v_name_1868_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1877_, v___y_1870_, v___y_1871_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1879_, lean_object* v_decl_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_registerTagAttribute___lam__4(v_name_1879_, v_decl_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_decl_1880_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1885_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_registerTagAttribute___lam__5(v___x_1890_, v_x_1891_, v_x_1892_);
lean_dec_ref(v_x_1892_);
lean_dec_ref(v_x_1891_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_registerTagAttribute___lam__6(v___x_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1901_, lean_object* v_declName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1906_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1907_ = l_Lean_MessageData_ofName(v_attrName_1901_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = 0;
v___x_1912_ = l_Lean_MessageData_ofConstName(v_declName_1902_, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1910_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1915_, v___y_1903_, v___y_1904_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1917_, lean_object* v_declName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1917_, v_declName_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1923_, lean_object* v_declName_1924_, lean_object* v_asyncPrefix_x3f_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___y_1930_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1925_) == 0)
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_MessageData_nil;
v___y_1930_ = v___x_1943_;
goto v___jp_1929_;
}
else
{
lean_object* v_val_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_val_1944_ = lean_ctor_get(v_asyncPrefix_x3f_1925_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v_asyncPrefix_x3f_1925_, 1);
v___x_1945_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1946_ = l_Lean_MessageData_ofName(v_val_1944_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___y_1930_ = v___x_1949_;
goto v___jp_1929_;
}
v___jp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1931_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1932_ = l_Lean_MessageData_ofName(v_attrName_1923_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = 0;
v___x_1937_ = l_Lean_MessageData_ofConstName(v_declName_1924_, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___y_1930_);
v___x_1942_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1941_, v___y_1926_, v___y_1927_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1950_, lean_object* v_declName_1951_, lean_object* v_asyncPrefix_x3f_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1950_, v_declName_1951_, v_asyncPrefix_x3f_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1957_, uint8_t v_kind_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___y_1968_; 
v___x_1962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1963_ = l_Lean_MessageData_ofName(v_name_1957_);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
switch(v_kind_1958_)
{
case 0:
{
lean_object* v___x_1975_; 
v___x_1975_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1968_ = v___x_1975_;
goto v___jp_1967_;
}
case 1:
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1968_ = v___x_1976_;
goto v___jp_1967_;
}
default: 
{
lean_object* v___x_1977_; 
v___x_1977_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1968_ = v___x_1977_;
goto v___jp_1967_;
}
}
v___jp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_inc_ref(v___y_1968_);
v___x_1969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1968_);
v___x_1970_ = l_Lean_MessageData_ofFormat(v___x_1969_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1966_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1973_, v___y_1959_, v___y_1960_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1978_, lean_object* v_kind_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
uint8_t v_kind_boxed_1983_; lean_object* v_res_1984_; 
v_kind_boxed_1983_ = lean_unbox(v_kind_1979_);
v_res_1984_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1978_, v_kind_boxed_1983_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1985_, lean_object* v_a_1986_, lean_object* v_name_1987_, lean_object* v_decl_1988_, lean_object* v_stx_1989_, uint8_t v_kind_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1989_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2043_) == 0)
{
uint8_t v___x_2044_; uint8_t v___x_2045_; 
lean_dec_ref_known(v___x_2043_, 1);
v___x_2044_ = 0;
v___x_2045_ = l_Lean_instBEqAttributeKind_beq(v_kind_1990_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v_decl_1988_);
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
v___x_2046_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1987_, v_kind_1990_, v___y_1991_, v___y_1992_);
return v___x_2046_;
}
else
{
goto v___jp_2038_;
}
}
else
{
lean_dec(v_decl_1988_);
lean_dec(v_name_1987_);
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
return v___x_2043_;
}
v___jp_1994_:
{
lean_object* v___x_1997_; 
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v_decl_1988_);
v___x_1997_ = lean_apply_4(v_validate_1985_, v_decl_1988_, v___y_1995_, v___y_1996_, lean_box(0));
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2027_; 
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2028_);
v___x_1999_ = v___x_1997_;
v_isShared_2000_ = v_isSharedCheck_2027_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v___x_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2027_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v_toEnvExtension_2002_; lean_object* v_env_2003_; lean_object* v_nextMacroScope_2004_; lean_object* v_ngen_2005_; lean_object* v_auxDeclNGen_2006_; lean_object* v_traceState_2007_; lean_object* v_messages_2008_; lean_object* v_infoState_2009_; lean_object* v_snapshotTasks_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2025_; 
v___x_2001_ = lean_st_ref_take(v___y_1996_);
v_toEnvExtension_2002_ = lean_ctor_get(v_a_1986_, 0);
v_env_2003_ = lean_ctor_get(v___x_2001_, 0);
v_nextMacroScope_2004_ = lean_ctor_get(v___x_2001_, 1);
v_ngen_2005_ = lean_ctor_get(v___x_2001_, 2);
v_auxDeclNGen_2006_ = lean_ctor_get(v___x_2001_, 3);
v_traceState_2007_ = lean_ctor_get(v___x_2001_, 4);
v_messages_2008_ = lean_ctor_get(v___x_2001_, 6);
v_infoState_2009_ = lean_ctor_get(v___x_2001_, 7);
v_snapshotTasks_2010_ = lean_ctor_get(v___x_2001_, 8);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2001_, 5);
lean_dec(v_unused_2026_);
v___x_2012_ = v___x_2001_;
v_isShared_2013_ = v_isSharedCheck_2025_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snapshotTasks_2010_);
lean_inc(v_infoState_2009_);
lean_inc(v_messages_2008_);
lean_inc(v_traceState_2007_);
lean_inc(v_auxDeclNGen_2006_);
lean_inc(v_ngen_2005_);
lean_inc(v_nextMacroScope_2004_);
lean_inc(v_env_2003_);
lean_dec(v___x_2001_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2025_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_asyncMode_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v_asyncMode_2014_ = lean_ctor_get(v_toEnvExtension_2002_, 2);
lean_inc(v_asyncMode_2014_);
v___x_2015_ = lean_box(0);
lean_inc(v_decl_1988_);
v___x_2016_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1986_, v_env_2003_, v_decl_1988_, v_asyncMode_2014_, v_decl_1988_);
lean_dec(v_asyncMode_2014_);
v___x_2017_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 5, v___x_2017_);
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2019_ = v___x_2012_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_nextMacroScope_2004_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_ngen_2005_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_auxDeclNGen_2006_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_traceState_2007_);
lean_ctor_set(v_reuseFailAlloc_2024_, 5, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2024_, 6, v_messages_2008_);
lean_ctor_set(v_reuseFailAlloc_2024_, 7, v_infoState_2009_);
lean_ctor_set(v_reuseFailAlloc_2024_, 8, v_snapshotTasks_2010_);
v___x_2019_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_st_ref_put(v___y_1996_, v___x_2019_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2015_);
v___x_2022_ = v___x_1999_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2015_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_dec(v_decl_1988_);
lean_dec_ref(v_a_1986_);
return v___x_1997_;
}
}
v___jp_2029_:
{
lean_object* v_toEnvExtension_2033_; lean_object* v_asyncMode_2034_; uint8_t v___x_2035_; 
v_toEnvExtension_2033_ = lean_ctor_get(v_a_1986_, 0);
v_asyncMode_2034_ = lean_ctor_get(v_toEnvExtension_2033_, 2);
lean_inc(v_decl_1988_);
lean_inc_ref(v___y_2030_);
v___x_2035_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2030_, v_decl_1988_, v_asyncMode_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
v___x_2036_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2030_);
v___x_2037_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1987_, v_decl_1988_, v___x_2036_, v___y_2031_, v___y_2032_);
return v___x_2037_;
}
else
{
lean_dec_ref(v___y_2030_);
lean_dec(v_name_1987_);
v___y_1995_ = v___y_2031_;
v___y_1996_ = v___y_2032_;
goto v___jp_1994_;
}
}
v___jp_2038_:
{
lean_object* v___x_2039_; lean_object* v_env_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_st_ref_get(v___y_1992_);
v_env_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_ref(v_env_2040_);
lean_dec(v___x_2039_);
v___x_2041_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2040_, v_decl_1988_);
if (lean_obj_tag(v___x_2041_) == 0)
{
v___y_2030_ = v_env_2040_;
v___y_2031_ = v___y_1991_;
v___y_2032_ = v___y_1992_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref_known(v___x_2041_, 1);
lean_dec_ref(v_env_2040_);
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
v___x_2042_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1987_, v_decl_1988_, v___y_1991_, v___y_1992_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2047_, lean_object* v_a_2048_, lean_object* v_name_2049_, lean_object* v_decl_2050_, lean_object* v_stx_2051_, lean_object* v_kind_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v_kind_boxed_2056_; lean_object* v_res_2057_; 
v_kind_boxed_2056_ = lean_unbox(v_kind_2052_);
v_res_2057_ = l_Lean_registerTagAttribute___lam__7(v_validate_2047_, v_a_2048_, v_name_2049_, v_decl_2050_, v_stx_2051_, v_kind_boxed_2056_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2057_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___f_2064_; 
v___x_2063_ = l_Lean_NameSet_empty;
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2064_, 0, v___x_2063_);
return v___f_2064_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___f_2066_; 
v___x_2065_ = l_Lean_NameSet_empty;
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2066_, 0, v___x_2065_);
return v___f_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2069_, lean_object* v_descr_2070_, lean_object* v_validate_2071_, lean_object* v_ref_2072_, uint8_t v_applicationTime_2073_, lean_object* v_asyncMode_2074_){
_start:
{
lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___f_2076_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2077_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2078_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2079_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2069_);
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2080_, 0, v_name_2069_);
v___f_2081_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2082_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2083_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2072_);
v___x_2084_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2084_, 0, v_ref_2072_);
lean_ctor_set(v___x_2084_, 1, v___f_2082_);
lean_ctor_set(v___x_2084_, 2, v___f_2081_);
lean_ctor_set(v___x_2084_, 3, v___f_2079_);
lean_ctor_set(v___x_2084_, 4, v___f_2078_);
lean_ctor_set(v___x_2084_, 5, v___f_2077_);
lean_ctor_set(v___x_2084_, 6, v_asyncMode_2074_);
lean_ctor_set(v___x_2084_, 7, v___x_2083_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v___f_2076_);
v___x_2086_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2085_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc_n(v_a_2087_, 2);
lean_dec_ref_known(v___x_2086_, 1);
lean_inc(v_name_2069_);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2088_, 0, v_validate_2071_);
lean_closure_set(v___f_2088_, 1, v_a_2087_);
lean_closure_set(v___f_2088_, 2, v_name_2069_);
v___x_2089_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2089_, 0, v_ref_2072_);
lean_ctor_set(v___x_2089_, 1, v_name_2069_);
lean_ctor_set(v___x_2089_, 2, v_descr_2070_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*3, v_applicationTime_2073_);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___f_2088_);
lean_ctor_set(v___x_2090_, 2, v___f_2080_);
lean_inc_ref(v___x_2090_);
v___x_2091_ = l_Lean_registerBuiltinAttribute(v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2099_; 
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v___x_2091_, 0);
lean_dec(v_unused_2100_);
v___x_2093_ = v___x_2091_;
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
else
{
lean_dec(v___x_2091_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2090_);
lean_ctor_set(v___x_2095_, 1, v_a_2087_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2095_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref_known(v___x_2090_, 3);
lean_dec(v_a_2087_);
v_a_2101_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2091_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2091_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v___f_2080_);
lean_dec(v_ref_2072_);
lean_dec_ref(v_validate_2071_);
lean_dec_ref(v_descr_2070_);
lean_dec(v_name_2069_);
v_a_2109_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2086_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2086_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2117_, lean_object* v_descr_2118_, lean_object* v_validate_2119_, lean_object* v_ref_2120_, lean_object* v_applicationTime_2121_, lean_object* v_asyncMode_2122_, lean_object* v_a_2123_){
_start:
{
uint8_t v_applicationTime_boxed_2124_; lean_object* v_res_2125_; 
v_applicationTime_boxed_2124_ = lean_unbox(v_applicationTime_2121_);
v_res_2125_ = l_Lean_registerTagAttribute(v_name_2117_, v_descr_2118_, v_validate_2119_, v_ref_2120_, v_applicationTime_boxed_2124_, v_asyncMode_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2126_, lean_object* v_t_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2126_, v_t_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2129_, lean_object* v_as_2130_, lean_object* v_lo_2131_, lean_object* v_hi_2132_, lean_object* v_w_2133_, lean_object* v_hlo_2134_, lean_object* v_hhi_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2129_, v_as_2130_, v_lo_2131_, v_hi_2132_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2137_, lean_object* v_as_2138_, lean_object* v_lo_2139_, lean_object* v_hi_2140_, lean_object* v_w_2141_, lean_object* v_hlo_2142_, lean_object* v_hhi_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2137_, v_as_2138_, v_lo_2139_, v_hi_2140_, v_w_2141_, v_hlo_2142_, v_hhi_2143_);
lean_dec(v_hi_2140_);
lean_dec(v_n_2137_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2145_, lean_object* v_attrName_2146_, lean_object* v_declName_2147_, lean_object* v_asyncPrefix_x3f_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2146_, v_declName_2147_, v_asyncPrefix_x3f_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_attrName_2154_, lean_object* v_declName_2155_, lean_object* v_asyncPrefix_x3f_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2153_, v_attrName_2154_, v_declName_2155_, v_asyncPrefix_x3f_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2161_, lean_object* v_attrName_2162_, lean_object* v_declName_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2162_, v_declName_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_attrName_2169_, lean_object* v_declName_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2168_, v_attrName_2169_, v_declName_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2175_, lean_object* v_name_2176_, uint8_t v_kind_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2176_, v_kind_2177_, v___y_2178_, v___y_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2182_, lean_object* v_name_2183_, lean_object* v_kind_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_kind_boxed_2188_; lean_object* v_res_2189_; 
v_kind_boxed_2188_ = lean_unbox(v_kind_2184_);
v_res_2189_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2182_, v_name_2183_, v_kind_boxed_2188_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2190_, lean_object* v_lo_2191_, lean_object* v_hi_2192_, lean_object* v_hhi_2193_, lean_object* v_pivot_2194_, lean_object* v_as_2195_, lean_object* v_i_2196_, lean_object* v_k_2197_, lean_object* v_ilo_2198_, lean_object* v_ik_2199_, lean_object* v_w_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2192_, v_pivot_2194_, v_as_2195_, v_i_2196_, v_k_2197_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2202_, lean_object* v_lo_2203_, lean_object* v_hi_2204_, lean_object* v_hhi_2205_, lean_object* v_pivot_2206_, lean_object* v_as_2207_, lean_object* v_i_2208_, lean_object* v_k_2209_, lean_object* v_ilo_2210_, lean_object* v_ik_2211_, lean_object* v_w_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2202_, v_lo_2203_, v_hi_2204_, v_hhi_2205_, v_pivot_2206_, v_as_2207_, v_i_2208_, v_k_2209_, v_ilo_2210_, v_ik_2211_, v_w_2212_);
lean_dec(v_pivot_2206_);
lean_dec(v_hi_2204_);
lean_dec(v_lo_2203_);
lean_dec(v_n_2202_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2214_, lean_object* v_decl_2215_, lean_object* v_env_2216_){
_start:
{
lean_object* v_ext_2217_; lean_object* v_toEnvExtension_2218_; lean_object* v_asyncMode_2219_; lean_object* v___x_2220_; 
v_ext_2217_ = lean_ctor_get(v_attr_2214_, 1);
lean_inc_ref(v_ext_2217_);
lean_dec_ref(v_attr_2214_);
v_toEnvExtension_2218_ = lean_ctor_get(v_ext_2217_, 0);
v_asyncMode_2219_ = lean_ctor_get(v_toEnvExtension_2218_, 2);
lean_inc(v_asyncMode_2219_);
lean_inc(v_decl_2215_);
v___x_2220_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2217_, v_env_2216_, v_decl_2215_, v_asyncMode_2219_, v_decl_2215_);
lean_dec(v_asyncMode_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2221_, lean_object* v___f_2222_, lean_object* v_____r_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_apply_1(v_modifyEnv_2221_, v___f_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2225_, lean_object* v_env_2226_, lean_object* v_decl_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_toBind_2230_, lean_object* v___f_2231_, lean_object* v_modifyEnv_2232_, lean_object* v___f_2233_, lean_object* v_____r_2234_){
_start:
{
lean_object* v_ext_2235_; lean_object* v_toEnvExtension_2236_; lean_object* v_attr_2237_; lean_object* v_asyncMode_2238_; uint8_t v___x_2239_; 
v_ext_2235_ = lean_ctor_get(v_attr_2225_, 1);
v_toEnvExtension_2236_ = lean_ctor_get(v_ext_2235_, 0);
lean_inc_ref(v_toEnvExtension_2236_);
v_attr_2237_ = lean_ctor_get(v_attr_2225_, 0);
lean_inc_ref(v_attr_2237_);
lean_dec_ref(v_attr_2225_);
v_asyncMode_2238_ = lean_ctor_get(v_toEnvExtension_2236_, 2);
lean_inc(v_asyncMode_2238_);
lean_dec_ref(v_toEnvExtension_2236_);
lean_inc(v_decl_2227_);
lean_inc_ref(v_env_2226_);
v___x_2239_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2226_, v_decl_2227_, v_asyncMode_2238_);
lean_dec(v_asyncMode_2238_);
if (v___x_2239_ == 0)
{
lean_object* v_toAttributeImplCore_2240_; lean_object* v_name_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v___f_2233_);
lean_dec(v_modifyEnv_2232_);
v_toAttributeImplCore_2240_ = lean_ctor_get(v_attr_2237_, 0);
lean_inc_ref(v_toAttributeImplCore_2240_);
lean_dec_ref(v_attr_2237_);
v_name_2241_ = lean_ctor_get(v_toAttributeImplCore_2240_, 1);
lean_inc(v_name_2241_);
lean_dec_ref(v_toAttributeImplCore_2240_);
v___x_2242_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2226_);
v___x_2243_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2228_, v_inst_2229_, v_name_2241_, v_decl_2227_, v___x_2242_);
v___x_2244_ = lean_apply_4(v_toBind_2230_, lean_box(0), lean_box(0), v___x_2243_, v___f_2231_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; 
lean_dec_ref(v_attr_2237_);
lean_dec(v___f_2231_);
lean_dec(v_toBind_2230_);
lean_dec_ref(v_inst_2229_);
lean_dec_ref(v_inst_2228_);
lean_dec(v_decl_2227_);
lean_dec_ref(v_env_2226_);
v___x_2245_ = lean_apply_1(v_modifyEnv_2232_, v___f_2233_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2246_, lean_object* v_____r_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_apply_1(v___f_2246_, v_____r_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2249_, lean_object* v_decl_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_toBind_2253_, lean_object* v___f_2254_, lean_object* v_modifyEnv_2255_, lean_object* v___f_2256_, lean_object* v_env_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; 
lean_inc_ref(v___f_2256_);
lean_inc(v_modifyEnv_2255_);
lean_inc(v___f_2254_);
lean_inc(v_toBind_2253_);
lean_inc_ref(v_inst_2252_);
lean_inc_ref(v_inst_2251_);
lean_inc(v_decl_2250_);
lean_inc_ref(v_env_2257_);
lean_inc_ref(v_attr_2249_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2258_, 0, v_attr_2249_);
lean_closure_set(v___f_2258_, 1, v_env_2257_);
lean_closure_set(v___f_2258_, 2, v_decl_2250_);
lean_closure_set(v___f_2258_, 3, v_inst_2251_);
lean_closure_set(v___f_2258_, 4, v_inst_2252_);
lean_closure_set(v___f_2258_, 5, v_toBind_2253_);
lean_closure_set(v___f_2258_, 6, v___f_2254_);
lean_closure_set(v___f_2258_, 7, v_modifyEnv_2255_);
lean_closure_set(v___f_2258_, 8, v___f_2256_);
v___x_2259_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2257_, v_decl_2250_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v___f_2258_);
v___x_2260_ = lean_box(0);
v___x_2261_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2249_, v_env_2257_, v_decl_2250_, v_inst_2251_, v_inst_2252_, v_toBind_2253_, v___f_2254_, v_modifyEnv_2255_, v___f_2256_, v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v_attr_2262_; lean_object* v_toAttributeImplCore_2263_; lean_object* v_name_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref_known(v___x_2259_, 1);
lean_dec_ref(v_env_2257_);
lean_dec_ref(v___f_2256_);
lean_dec(v_modifyEnv_2255_);
lean_dec(v___f_2254_);
v_attr_2262_ = lean_ctor_get(v_attr_2249_, 0);
lean_inc_ref(v_attr_2262_);
lean_dec_ref(v_attr_2249_);
v_toAttributeImplCore_2263_ = lean_ctor_get(v_attr_2262_, 0);
lean_inc_ref(v_toAttributeImplCore_2263_);
lean_dec_ref(v_attr_2262_);
v_name_2264_ = lean_ctor_get(v_toAttributeImplCore_2263_, 1);
lean_inc(v_name_2264_);
lean_dec_ref(v_toAttributeImplCore_2263_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2265_, 0, v___f_2258_);
v___x_2266_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2251_, v_inst_2252_, v_name_2264_, v_decl_2250_);
v___x_2267_ = lean_apply_4(v_toBind_2253_, lean_box(0), lean_box(0), v___x_2266_, v___f_2265_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_attr_2271_, lean_object* v_decl_2272_){
_start:
{
lean_object* v_toBind_2273_; lean_object* v_getEnv_2274_; lean_object* v_modifyEnv_2275_; lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; 
v_toBind_2273_ = lean_ctor_get(v_inst_2268_, 1);
lean_inc_n(v_toBind_2273_, 2);
v_getEnv_2274_ = lean_ctor_get(v_inst_2270_, 0);
lean_inc(v_getEnv_2274_);
v_modifyEnv_2275_ = lean_ctor_get(v_inst_2270_, 1);
lean_inc_n(v_modifyEnv_2275_, 2);
lean_dec_ref(v_inst_2270_);
lean_inc(v_decl_2272_);
lean_inc_ref(v_attr_2271_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2276_, 0, v_attr_2271_);
lean_closure_set(v___f_2276_, 1, v_decl_2272_);
lean_inc_ref(v___f_2276_);
v___f_2277_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2277_, 0, v_modifyEnv_2275_);
lean_closure_set(v___f_2277_, 1, v___f_2276_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2278_, 0, v_attr_2271_);
lean_closure_set(v___f_2278_, 1, v_decl_2272_);
lean_closure_set(v___f_2278_, 2, v_inst_2268_);
lean_closure_set(v___f_2278_, 3, v_inst_2269_);
lean_closure_set(v___f_2278_, 4, v_toBind_2273_);
lean_closure_set(v___f_2278_, 5, v___f_2277_);
lean_closure_set(v___f_2278_, 6, v_modifyEnv_2275_);
lean_closure_set(v___f_2278_, 7, v___f_2276_);
v___x_2279_ = lean_apply_4(v_toBind_2273_, lean_box(0), lean_box(0), v_getEnv_2274_, v___f_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_attr_2284_, lean_object* v_decl_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2281_, v_inst_2282_, v_inst_2283_, v_attr_2284_, v_decl_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2287_, lean_object* v_as_2288_, lean_object* v_k_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v_m_2294_; lean_object* v_a_2295_; uint8_t v___x_2296_; 
v___x_2292_ = lean_nat_add(v_x_2290_, v_x_2291_);
v___x_2293_ = lean_unsigned_to_nat(1u);
v_m_2294_ = lean_nat_shiftr(v___x_2292_, v___x_2293_);
lean_dec(v___x_2292_);
v_a_2295_ = lean_array_fget_borrowed(v_as_2288_, v_m_2294_);
v___x_2296_ = l_Lean_Name_quickLt(v_a_2295_, v_k_2289_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; uint8_t v___x_2298_; 
lean_dec(v_x_2291_);
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = l_Lean_Name_quickLt(v_k_2289_, v_a_2295_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; 
lean_dec(v_m_2294_);
lean_dec(v_x_2290_);
v___x_2299_ = lean_nat_dec_le(v___x_2297_, v___y_2287_);
return v___x_2299_;
}
else
{
uint8_t v___x_2300_; lean_object* v___x_2301_; uint8_t v___y_2303_; 
v___x_2300_ = lean_nat_dec_eq(v_m_2294_, v___x_2297_);
v___x_2301_ = lean_nat_sub(v_m_2294_, v___x_2293_);
lean_dec(v_m_2294_);
if (v___x_2300_ == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_nat_dec_lt(v___x_2301_, v_x_2290_);
v___y_2303_ = v___x_2305_;
goto v___jp_2302_;
}
else
{
v___y_2303_ = v___x_2300_;
goto v___jp_2302_;
}
v___jp_2302_:
{
if (v___y_2303_ == 0)
{
v_x_2291_ = v___x_2301_;
goto _start;
}
else
{
lean_dec(v___x_2301_);
lean_dec(v_x_2290_);
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
lean_dec(v_x_2290_);
v___x_2306_ = lean_nat_add(v_m_2294_, v___x_2293_);
lean_dec(v_m_2294_);
v___x_2307_ = lean_nat_dec_le(v___x_2306_, v_x_2291_);
if (v___x_2307_ == 0)
{
lean_dec(v___x_2306_);
lean_dec(v_x_2291_);
return v___x_2307_;
}
else
{
v_x_2290_ = v___x_2306_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2309_, lean_object* v_as_2310_, lean_object* v_k_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2309_, v_as_2310_, v_k_2311_, v_x_2312_, v_x_2313_);
lean_dec(v_k_2311_);
lean_dec_ref(v_as_2310_);
lean_dec(v___y_2309_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2316_, lean_object* v_env_2317_, lean_object* v_decl_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_box(1);
v___x_2320_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2317_, v_decl_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_ext_2321_; lean_object* v_toEnvExtension_2322_; lean_object* v_asyncMode_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_ext_2321_ = lean_ctor_get(v_attr_2316_, 1);
v_toEnvExtension_2322_ = lean_ctor_get(v_ext_2321_, 0);
v_asyncMode_2323_ = lean_ctor_get(v_toEnvExtension_2322_, 2);
lean_inc(v_decl_2318_);
v___x_2324_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2319_, v_ext_2321_, v_env_2317_, v_asyncMode_2323_, v_decl_2318_);
v___x_2325_ = l_Lean_NameSet_contains(v___x_2324_, v_decl_2318_);
lean_dec(v_decl_2318_);
lean_dec(v___x_2324_);
return v___x_2325_;
}
else
{
lean_object* v_val_2326_; lean_object* v_ext_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_val_2326_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_val_2326_);
lean_dec_ref_known(v___x_2320_, 1);
v_ext_2327_ = lean_ctor_get(v_attr_2316_, 1);
v___x_2328_ = 0;
v___x_2329_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2319_, v_ext_2327_, v_env_2317_, v_val_2326_, v___x_2328_);
lean_dec(v_val_2326_);
lean_dec_ref(v_env_2317_);
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = lean_array_get_size(v___x_2329_);
v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec_ref(v___x_2329_);
lean_dec(v_decl_2318_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_sub(v___x_2331_, v___x_2333_);
v___x_2335_ = lean_nat_dec_le(v___x_2330_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2329_);
lean_dec(v_decl_2318_);
return v___x_2335_;
}
else
{
uint8_t v___x_2336_; 
lean_inc(v___x_2334_);
v___x_2336_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2334_, v___x_2329_, v_decl_2318_, v___x_2330_, v___x_2334_);
lean_dec(v_decl_2318_);
lean_dec_ref(v___x_2329_);
lean_dec(v___x_2334_);
return v___x_2336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2337_, lean_object* v_env_2338_, lean_object* v_decl_2339_){
_start:
{
uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_res_2340_ = l_Lean_TagAttribute_hasTag(v_attr_2337_, v_env_2338_, v_decl_2339_);
lean_dec_ref(v_attr_2337_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2342_, lean_object* v_as_2343_, lean_object* v_k_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2342_, v_as_2343_, v_k_2344_, v_x_2345_, v_x_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2349_, lean_object* v_as_2350_, lean_object* v_k_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2349_, v_as_2350_, v_k_2351_, v_x_2352_, v_x_2353_, v_x_2354_);
lean_dec(v_k_2351_);
lean_dec_ref(v_as_2350_);
lean_dec(v___y_2349_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2362_, v___y_2363_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_x_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2366_, lean_object* v_x_2367_){
_start:
{
lean_inc_ref(v_s_2366_);
return v_s_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2368_, lean_object* v_x_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2368_, v_x_2369_);
lean_dec_ref(v_x_2369_);
lean_dec_ref(v_s_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2378_, v_x_2379_);
lean_dec_ref(v_x_2379_);
lean_dec_ref(v_x_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_box(0);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2383_);
lean_dec_ref(v_x_2383_);
return v_res_2384_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2389_; lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___f_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___f_2389_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2390_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2391_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2392_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2395_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
lean_ctor_set(v___x_2395_, 1, v___x_2393_);
lean_ctor_set(v___x_2395_, 2, v___f_2392_);
lean_ctor_set(v___x_2395_, 3, v___f_2391_);
lean_ctor_set(v___x_2395_, 4, v___f_2390_);
lean_ctor_set(v___x_2395_, 5, v___f_2389_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2396_ = 0;
v___x_2397_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2398_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2399_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___x_2397_);
lean_ctor_set_uint8(v___x_2399_, sizeof(void*)*2, v___x_2396_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2403_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2413_, lean_object* v_p_2414_){
_start:
{
lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2433_; 
v_fst_2415_ = lean_ctor_get(v_x_2413_, 0);
v_snd_2416_ = lean_ctor_get(v_x_2413_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_x_2413_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2418_ = v_x_2413_;
v_isShared_2419_ = v_isSharedCheck_2433_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snd_2416_);
lean_inc(v_fst_2415_);
lean_dec(v_x_2413_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2433_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_fst_2420_; lean_object* v_snd_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2432_; 
v_fst_2420_ = lean_ctor_get(v_p_2414_, 0);
v_snd_2421_ = lean_ctor_get(v_p_2414_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_p_2414_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2423_ = v_p_2414_;
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_snd_2421_);
lean_inc(v_fst_2420_);
lean_dec(v_p_2414_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2432_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
lean_inc(v_fst_2420_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 1);
lean_ctor_set(v___x_2418_, 1, v_fst_2415_);
lean_ctor_set(v___x_2418_, 0, v_fst_2420_);
v___x_2426_ = v___x_2418_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_fst_2420_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_fst_2415_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2420_, v_snd_2421_, v_snd_2416_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v___x_2427_);
lean_ctor_set(v___x_2423_, 0, v___x_2426_);
v___x_2429_ = v___x_2423_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2434_, lean_object* v_x_2435_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v_k_2436_; lean_object* v_v_2437_; lean_object* v_l_2438_; lean_object* v_r_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_k_2436_ = lean_ctor_get(v_x_2435_, 1);
v_v_2437_ = lean_ctor_get(v_x_2435_, 2);
v_l_2438_ = lean_ctor_get(v_x_2435_, 3);
v_r_2439_ = lean_ctor_get(v_x_2435_, 4);
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2434_, v_l_2438_);
lean_inc(v_v_2437_);
lean_inc(v_k_2436_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_k_2436_);
lean_ctor_set(v___x_2441_, 1, v_v_2437_);
v___x_2442_ = lean_array_push(v___x_2440_, v___x_2441_);
v_init_2434_ = v___x_2442_;
v_x_2435_ = v_r_2439_;
goto _start;
}
else
{
return v_init_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2444_, v_x_2445_);
lean_dec(v_x_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2447_, lean_object* v_as_2448_, size_t v_i_2449_, size_t v_stop_2450_, lean_object* v_b_2451_){
_start:
{
lean_object* v___y_2453_; uint8_t v___x_2457_; 
v___x_2457_ = lean_usize_dec_eq(v_i_2449_, v_stop_2450_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_array_uget_borrowed(v_as_2448_, v_i_2449_);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2447_, v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
v___y_2453_ = v_b_2451_;
goto v___jp_2452_;
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_val_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v___x_2459_, 1);
lean_inc(v___x_2458_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2458_);
lean_ctor_set(v___x_2461_, 1, v_val_2460_);
v___x_2462_ = lean_array_push(v_b_2451_, v___x_2461_);
v___y_2453_ = v___x_2462_;
goto v___jp_2452_;
}
}
else
{
return v_b_2451_;
}
v___jp_2452_:
{
size_t v___x_2454_; size_t v___x_2455_; 
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2449_, v___x_2454_);
v_i_2449_ = v___x_2455_;
v_b_2451_ = v___y_2453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2463_, lean_object* v_as_2464_, lean_object* v_i_2465_, lean_object* v_stop_2466_, lean_object* v_b_2467_){
_start:
{
size_t v_i_boxed_2468_; size_t v_stop_boxed_2469_; lean_object* v_res_2470_; 
v_i_boxed_2468_ = lean_unbox_usize(v_i_2465_);
lean_dec(v_i_2465_);
v_stop_boxed_2469_ = lean_unbox_usize(v_stop_2466_);
lean_dec(v_stop_2466_);
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2463_, v_as_2464_, v_i_boxed_2468_, v_stop_boxed_2469_, v_b_2467_);
lean_dec_ref(v_as_2464_);
lean_dec(v_snd_2463_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2471_, lean_object* v_as_2472_, lean_object* v_start_2473_, lean_object* v_stop_2474_){
_start:
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2476_ = lean_nat_dec_lt(v_start_2473_, v_stop_2474_);
if (v___x_2476_ == 0)
{
return v___x_2475_;
}
else
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = lean_array_get_size(v_as_2472_);
v___x_2478_ = lean_nat_dec_le(v_stop_2474_, v___x_2477_);
if (v___x_2478_ == 0)
{
uint8_t v___x_2479_; 
v___x_2479_ = lean_nat_dec_lt(v_start_2473_, v___x_2477_);
if (v___x_2479_ == 0)
{
return v___x_2475_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_usize_of_nat(v_start_2473_);
v___x_2481_ = lean_usize_of_nat(v___x_2477_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2471_, v_as_2472_, v___x_2480_, v___x_2481_, v___x_2475_);
return v___x_2482_;
}
}
else
{
size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = lean_usize_of_nat(v_start_2473_);
v___x_2484_ = lean_usize_of_nat(v_stop_2474_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2471_, v_as_2472_, v___x_2483_, v___x_2484_, v___x_2475_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2486_, lean_object* v_as_2487_, lean_object* v_start_2488_, lean_object* v_stop_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2486_, v_as_2487_, v_start_2488_, v_stop_2489_);
lean_dec(v_stop_2489_);
lean_dec(v_start_2488_);
lean_dec_ref(v_as_2487_);
lean_dec(v_snd_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2491_, lean_object* v_pivot_2492_, lean_object* v_as_2493_, lean_object* v_i_2494_, lean_object* v_k_2495_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_nat_dec_lt(v_k_2495_, v_hi_2491_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_dec(v_k_2495_);
v___x_2497_ = lean_array_fswap(v_as_2493_, v_i_2494_, v_hi_2491_);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_i_2494_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
return v___x_2498_;
}
else
{
lean_object* v___x_2499_; lean_object* v_fst_2500_; lean_object* v_fst_2501_; uint8_t v___x_2502_; 
v___x_2499_ = lean_array_fget_borrowed(v_as_2493_, v_k_2495_);
v_fst_2500_ = lean_ctor_get(v___x_2499_, 0);
v_fst_2501_ = lean_ctor_get(v_pivot_2492_, 0);
v___x_2502_ = l_Lean_Name_quickLt(v_fst_2500_, v_fst_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_nat_add(v_k_2495_, v___x_2503_);
lean_dec(v_k_2495_);
v_k_2495_ = v___x_2504_;
goto _start;
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2506_ = lean_array_fswap(v_as_2493_, v_i_2494_, v_k_2495_);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_add(v_i_2494_, v___x_2507_);
lean_dec(v_i_2494_);
v___x_2509_ = lean_nat_add(v_k_2495_, v___x_2507_);
lean_dec(v_k_2495_);
v_as_2493_ = v___x_2506_;
v_i_2494_ = v___x_2508_;
v_k_2495_ = v___x_2509_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2511_, lean_object* v_pivot_2512_, lean_object* v_as_2513_, lean_object* v_i_2514_, lean_object* v_k_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2511_, v_pivot_2512_, v_as_2513_, v_i_2514_, v_k_2515_);
lean_dec_ref(v_pivot_2512_);
lean_dec(v_hi_2511_);
return v_res_2516_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2517_, lean_object* v_b_2518_){
_start:
{
lean_object* v_fst_2519_; lean_object* v_fst_2520_; uint8_t v___x_2521_; 
v_fst_2519_ = lean_ctor_get(v_a_2517_, 0);
v_fst_2520_ = lean_ctor_get(v_b_2518_, 0);
v___x_2521_ = l_Lean_Name_quickLt(v_fst_2519_, v_fst_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2522_, lean_object* v_b_2523_){
_start:
{
uint8_t v_res_2524_; lean_object* v_r_2525_; 
v_res_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2522_, v_b_2523_);
lean_dec_ref(v_b_2523_);
lean_dec_ref(v_a_2522_);
v_r_2525_ = lean_box(v_res_2524_);
return v_r_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2526_, lean_object* v_as_2527_, lean_object* v_lo_2528_, lean_object* v_hi_2529_){
_start:
{
lean_object* v___y_2531_; uint8_t v___x_2541_; 
v___x_2541_ = lean_nat_dec_lt(v_lo_2528_, v_hi_2529_);
if (v___x_2541_ == 0)
{
lean_dec(v_lo_2528_);
return v_as_2527_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_mid_2544_; lean_object* v___y_2546_; lean_object* v___y_2552_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2542_ = lean_nat_add(v_lo_2528_, v_hi_2529_);
v___x_2543_ = lean_unsigned_to_nat(1u);
v_mid_2544_ = lean_nat_shiftr(v___x_2542_, v___x_2543_);
lean_dec(v___x_2542_);
v___x_2557_ = lean_array_fget_borrowed(v_as_2527_, v_mid_2544_);
v___x_2558_ = lean_array_fget_borrowed(v_as_2527_, v_lo_2528_);
v___x_2559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2557_, v___x_2558_);
if (v___x_2559_ == 0)
{
v___y_2552_ = v_as_2527_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_array_fswap(v_as_2527_, v_lo_2528_, v_mid_2544_);
v___y_2552_ = v___x_2560_;
goto v___jp_2551_;
}
v___jp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2547_ = lean_array_fget_borrowed(v___y_2546_, v_mid_2544_);
v___x_2548_ = lean_array_fget_borrowed(v___y_2546_, v_hi_2529_);
v___x_2549_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_dec(v_mid_2544_);
v___y_2531_ = v___y_2546_;
goto v___jp_2530_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_array_fswap(v___y_2546_, v_mid_2544_, v_hi_2529_);
lean_dec(v_mid_2544_);
v___y_2531_ = v___x_2550_;
goto v___jp_2530_;
}
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2553_ = lean_array_fget_borrowed(v___y_2552_, v_hi_2529_);
v___x_2554_ = lean_array_fget_borrowed(v___y_2552_, v_lo_2528_);
v___x_2555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2553_, v___x_2554_);
if (v___x_2555_ == 0)
{
v___y_2546_ = v___y_2552_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_array_fswap(v___y_2552_, v_lo_2528_, v_hi_2529_);
v___y_2546_ = v___x_2556_;
goto v___jp_2545_;
}
}
}
v___jp_2530_:
{
lean_object* v_pivot_2532_; lean_object* v___x_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; uint8_t v___x_2536_; 
v_pivot_2532_ = lean_array_fget(v___y_2531_, v_hi_2529_);
lean_inc_n(v_lo_2528_, 2);
v___x_2533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2529_, v_pivot_2532_, v___y_2531_, v_lo_2528_, v_lo_2528_);
lean_dec(v_pivot_2532_);
v_fst_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_fst_2534_);
v_snd_2535_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_snd_2535_);
lean_dec_ref(v___x_2533_);
v___x_2536_ = lean_nat_dec_le(v_hi_2529_, v_fst_2534_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2526_, v_snd_2535_, v_lo_2528_, v_fst_2534_);
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = lean_nat_add(v_fst_2534_, v___x_2538_);
lean_dec(v_fst_2534_);
v_as_2527_ = v___x_2537_;
v_lo_2528_ = v___x_2539_;
goto _start;
}
else
{
lean_dec(v_fst_2534_);
lean_dec(v_lo_2528_);
return v_snd_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2561_, lean_object* v_as_2562_, lean_object* v_lo_2563_, lean_object* v_hi_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2561_, v_as_2562_, v_lo_2563_, v_hi_2564_);
lean_dec(v_hi_2564_);
lean_dec(v_n_2561_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2566_, lean_object* v_env_2567_, lean_object* v_as_2568_, size_t v_i_2569_, size_t v_stop_2570_, lean_object* v_b_2571_){
_start:
{
lean_object* v___y_2573_; uint8_t v___x_2577_; 
v___x_2577_ = lean_usize_dec_eq(v_i_2569_, v_stop_2570_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v_fst_2579_; lean_object* v_snd_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2578_ = lean_array_uget_borrowed(v_as_2568_, v_i_2569_);
v_fst_2579_ = lean_ctor_get(v___x_2578_, 0);
v_snd_2580_ = lean_ctor_get(v___x_2578_, 1);
lean_inc_ref(v_filterExport_2566_);
lean_inc(v_snd_2580_);
lean_inc(v_fst_2579_);
lean_inc_ref(v_env_2567_);
v___x_2581_ = lean_apply_3(v_filterExport_2566_, v_env_2567_, v_fst_2579_, v_snd_2580_);
v___x_2582_ = lean_unbox(v___x_2581_);
if (v___x_2582_ == 0)
{
v___y_2573_ = v_b_2571_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2583_; 
lean_inc(v___x_2578_);
v___x_2583_ = lean_array_push(v_b_2571_, v___x_2578_);
v___y_2573_ = v___x_2583_;
goto v___jp_2572_;
}
}
else
{
lean_dec_ref(v_env_2567_);
lean_dec_ref(v_filterExport_2566_);
return v_b_2571_;
}
v___jp_2572_:
{
size_t v___x_2574_; size_t v___x_2575_; 
v___x_2574_ = ((size_t)1ULL);
v___x_2575_ = lean_usize_add(v_i_2569_, v___x_2574_);
v_i_2569_ = v___x_2575_;
v_b_2571_ = v___y_2573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2584_, lean_object* v_env_2585_, lean_object* v_as_2586_, lean_object* v_i_2587_, lean_object* v_stop_2588_, lean_object* v_b_2589_){
_start:
{
size_t v_i_boxed_2590_; size_t v_stop_boxed_2591_; lean_object* v_res_2592_; 
v_i_boxed_2590_ = lean_unbox_usize(v_i_2587_);
lean_dec(v_i_2587_);
v_stop_boxed_2591_ = lean_unbox_usize(v_stop_2588_);
lean_dec(v_stop_2588_);
v_res_2592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2584_, v_env_2585_, v_as_2586_, v_i_boxed_2590_, v_stop_boxed_2591_, v_b_2589_);
lean_dec_ref(v_as_2586_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2593_, uint8_t v_preserveOrder_2594_, lean_object* v_env_2595_, lean_object* v_x_2596_){
_start:
{
lean_object* v___y_2598_; 
if (v_preserveOrder_2594_ == 0)
{
lean_object* v_snd_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v_r_2617_; lean_object* v___x_2618_; lean_object* v___y_2620_; lean_object* v___y_2621_; uint8_t v___x_2623_; 
v_snd_2614_ = lean_ctor_get(v_x_2596_, 1);
lean_inc(v_snd_2614_);
lean_dec_ref(v_x_2596_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2617_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2616_, v_snd_2614_);
lean_dec(v_snd_2614_);
v___x_2618_ = lean_array_get_size(v_r_2617_);
v___x_2623_ = lean_nat_dec_eq(v___x_2618_, v___x_2615_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___y_2627_; uint8_t v___x_2629_; 
v___x_2624_ = lean_unsigned_to_nat(1u);
v___x_2625_ = lean_nat_sub(v___x_2618_, v___x_2624_);
v___x_2629_ = lean_nat_dec_le(v___x_2615_, v___x_2625_);
if (v___x_2629_ == 0)
{
lean_inc(v___x_2625_);
v___y_2627_ = v___x_2625_;
goto v___jp_2626_;
}
else
{
v___y_2627_ = v___x_2615_;
goto v___jp_2626_;
}
v___jp_2626_:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_nat_dec_le(v___y_2627_, v___x_2625_);
if (v___x_2628_ == 0)
{
lean_dec(v___x_2625_);
lean_inc(v___y_2627_);
v___y_2620_ = v___y_2627_;
v___y_2621_ = v___y_2627_;
goto v___jp_2619_;
}
else
{
v___y_2620_ = v___y_2627_;
v___y_2621_ = v___x_2625_;
goto v___jp_2619_;
}
}
}
else
{
v___y_2598_ = v_r_2617_;
goto v___jp_2597_;
}
v___jp_2619_:
{
lean_object* v___x_2622_; 
v___x_2622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2618_, v_r_2617_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
v___y_2598_ = v___x_2622_;
goto v___jp_2597_;
}
}
else
{
lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_fst_2630_ = lean_ctor_get(v_x_2596_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v_x_2596_, 1);
lean_inc(v_snd_2631_);
lean_dec_ref(v_x_2596_);
v___x_2632_ = lean_array_mk(v_fst_2630_);
v___x_2633_ = l_Array_reverse___redArg(v___x_2632_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_array_get_size(v___x_2633_);
v___x_2636_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2631_, v___x_2633_, v___x_2634_, v___x_2635_);
lean_dec_ref(v___x_2633_);
lean_dec(v_snd_2631_);
v___y_2598_ = v___x_2636_;
goto v___jp_2597_;
}
v___jp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_array_get_size(v___y_2598_);
v___x_2601_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2602_ = lean_nat_dec_lt(v___x_2599_, v___x_2600_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
lean_dec_ref(v_env_2595_);
lean_dec_ref(v_filterExport_2593_);
v___x_2603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2601_);
lean_ctor_set(v___x_2603_, 2, v___y_2598_);
return v___x_2603_;
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_nat_dec_le(v___x_2600_, v___x_2600_);
if (v___x_2604_ == 0)
{
if (v___x_2602_ == 0)
{
lean_object* v___x_2605_; 
lean_dec_ref(v_env_2595_);
lean_dec_ref(v_filterExport_2593_);
v___x_2605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2601_);
lean_ctor_set(v___x_2605_, 1, v___x_2601_);
lean_ctor_set(v___x_2605_, 2, v___y_2598_);
return v___x_2605_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = lean_usize_of_nat(v___x_2600_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2593_, v_env_2595_, v___y_2598_, v___x_2606_, v___x_2607_, v___x_2601_);
lean_inc_ref(v___x_2608_);
v___x_2609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_ctor_set(v___x_2609_, 2, v___y_2598_);
return v___x_2609_;
}
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = lean_usize_of_nat(v___x_2600_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2593_, v_env_2595_, v___y_2598_, v___x_2610_, v___x_2611_, v___x_2601_);
lean_inc_ref(v___x_2612_);
v___x_2613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_ctor_set(v___x_2613_, 2, v___y_2598_);
return v___x_2613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2637_, lean_object* v_preserveOrder_2638_, lean_object* v_env_2639_, lean_object* v_x_2640_){
_start:
{
uint8_t v_preserveOrder_boxed_2641_; lean_object* v_res_2642_; 
v_preserveOrder_boxed_2641_ = lean_unbox(v_preserveOrder_2638_);
v_res_2642_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2637_, v_preserveOrder_boxed_2641_, v_env_2639_, v_x_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2652_){
_start:
{
lean_object* v_snd_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2667_; 
v_snd_2653_ = lean_ctor_get(v_x_2652_, 1);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_x_2652_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v_x_2652_, 0);
lean_dec(v_unused_2668_);
v___x_2655_ = v_x_2652_;
v_isShared_2656_ = v_isSharedCheck_2667_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2653_);
lean_dec(v_x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2667_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___y_2659_; 
v___x_2657_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2653_) == 0)
{
lean_object* v_size_2665_; 
v_size_2665_ = lean_ctor_get(v_snd_2653_, 0);
lean_inc(v_size_2665_);
lean_dec_ref_known(v_snd_2653_, 5);
v___y_2659_ = v_size_2665_;
goto v___jp_2658_;
}
else
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_unsigned_to_nat(0u);
v___y_2659_ = v___x_2666_;
goto v___jp_2658_;
}
v___jp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2660_ = l_Nat_reprFast(v___y_2659_);
v___x_2661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 5);
lean_ctor_set(v___x_2655_, 1, v___x_2661_);
lean_ctor_set(v___x_2655_, 0, v___x_2657_);
v___x_2663_ = v___x_2655_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2671_);
lean_dec_ref(v_x_2671_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2679_, lean_object* v_x_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2679_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2684_, lean_object* v_x_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2684_, v_x_2685_, v___y_2686_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_x_2685_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2699_, uint8_t v_preserveOrder_2700_, lean_object* v_filterExport_2701_){
_start:
{
lean_object* v___f_2703_; lean_object* v___x_2704_; lean_object* v___f_2705_; lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___f_2703_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2704_ = lean_box(v_preserveOrder_2700_);
v___f_2705_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2705_, 0, v_filterExport_2701_);
lean_closure_set(v___f_2705_, 1, v___x_2704_);
v___f_2706_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2707_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2708_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2709_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2710_ = lean_box(2);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2712_, 0, v_ref_2699_);
lean_ctor_set(v___x_2712_, 1, v___f_2708_);
lean_ctor_set(v___x_2712_, 2, v___f_2709_);
lean_ctor_set(v___x_2712_, 3, v___f_2703_);
lean_ctor_set(v___x_2712_, 4, v___f_2705_);
lean_ctor_set(v___x_2712_, 5, v___f_2706_);
lean_ctor_set(v___x_2712_, 6, v___x_2710_);
lean_ctor_set(v___x_2712_, 7, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___f_2707_);
v___x_2714_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2715_, lean_object* v_preserveOrder_2716_, lean_object* v_filterExport_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_preserveOrder_boxed_2719_; lean_object* v_res_2720_; 
v_preserveOrder_boxed_2719_ = lean_unbox(v_preserveOrder_2716_);
v_res_2720_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2715_, v_preserveOrder_boxed_2719_, v_filterExport_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2721_, lean_object* v_ref_2722_, uint8_t v_preserveOrder_2723_, lean_object* v_filterExport_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2722_, v_preserveOrder_2723_, v_filterExport_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_ref_2728_, lean_object* v_preserveOrder_2729_, lean_object* v_filterExport_2730_, lean_object* v_a_2731_){
_start:
{
uint8_t v_preserveOrder_boxed_2732_; lean_object* v_res_2733_; 
v_preserveOrder_boxed_2732_ = lean_unbox(v_preserveOrder_2729_);
v_res_2733_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2727_, v_ref_2728_, v_preserveOrder_boxed_2732_, v_filterExport_2730_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2734_, lean_object* v_filterExport_2735_, lean_object* v_env_2736_, lean_object* v_as_2737_, size_t v_i_2738_, size_t v_stop_2739_, lean_object* v_b_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2735_, v_env_2736_, v_as_2737_, v_i_2738_, v_stop_2739_, v_b_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_filterExport_2743_, lean_object* v_env_2744_, lean_object* v_as_2745_, lean_object* v_i_2746_, lean_object* v_stop_2747_, lean_object* v_b_2748_){
_start:
{
size_t v_i_boxed_2749_; size_t v_stop_boxed_2750_; lean_object* v_res_2751_; 
v_i_boxed_2749_ = lean_unbox_usize(v_i_2746_);
lean_dec(v_i_2746_);
v_stop_boxed_2750_ = lean_unbox_usize(v_stop_2747_);
lean_dec(v_stop_2747_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2742_, v_filterExport_2743_, v_env_2744_, v_as_2745_, v_i_boxed_2749_, v_stop_boxed_2750_, v_b_2748_);
lean_dec_ref(v_as_2745_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2752_, lean_object* v_t_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2752_, v_t_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2755_, lean_object* v_t_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2755_, v_t_2756_);
lean_dec(v_t_2756_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2758_, lean_object* v_init_2759_, lean_object* v_t_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2759_, v_t_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_init_2763_, lean_object* v_t_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2762_, v_init_2763_, v_t_2764_);
lean_dec(v_t_2764_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2766_, lean_object* v_n_2767_, lean_object* v_as_2768_, lean_object* v_lo_2769_, lean_object* v_hi_2770_, lean_object* v_w_2771_, lean_object* v_hlo_2772_, lean_object* v_hhi_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2767_, v_as_2768_, v_lo_2769_, v_hi_2770_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2775_, lean_object* v_n_2776_, lean_object* v_as_2777_, lean_object* v_lo_2778_, lean_object* v_hi_2779_, lean_object* v_w_2780_, lean_object* v_hlo_2781_, lean_object* v_hhi_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2775_, v_n_2776_, v_as_2777_, v_lo_2778_, v_hi_2779_, v_w_2780_, v_hlo_2781_, v_hhi_2782_);
lean_dec(v_hi_2779_);
lean_dec(v_n_2776_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2784_, lean_object* v_snd_2785_, lean_object* v_as_2786_, lean_object* v_start_2787_, lean_object* v_stop_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2785_, v_as_2786_, v_start_2787_, v_stop_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2790_, lean_object* v_snd_2791_, lean_object* v_as_2792_, lean_object* v_start_2793_, lean_object* v_stop_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2790_, v_snd_2791_, v_as_2792_, v_start_2793_, v_stop_2794_);
lean_dec(v_stop_2794_);
lean_dec(v_start_2793_);
lean_dec_ref(v_as_2792_);
lean_dec(v_snd_2791_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2796_, lean_object* v_init_2797_, lean_object* v_x_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2797_, v_x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2800_, lean_object* v_init_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2800_, v_init_2801_, v_x_2802_);
lean_dec(v_x_2802_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2804_, lean_object* v_n_2805_, lean_object* v_lo_2806_, lean_object* v_hi_2807_, lean_object* v_hhi_2808_, lean_object* v_pivot_2809_, lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_k_2812_, lean_object* v_ilo_2813_, lean_object* v_ik_2814_, lean_object* v_w_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2807_, v_pivot_2809_, v_as_2810_, v_i_2811_, v_k_2812_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_n_2818_, lean_object* v_lo_2819_, lean_object* v_hi_2820_, lean_object* v_hhi_2821_, lean_object* v_pivot_2822_, lean_object* v_as_2823_, lean_object* v_i_2824_, lean_object* v_k_2825_, lean_object* v_ilo_2826_, lean_object* v_ik_2827_, lean_object* v_w_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2817_, v_n_2818_, v_lo_2819_, v_hi_2820_, v_hhi_2821_, v_pivot_2822_, v_as_2823_, v_i_2824_, v_k_2825_, v_ilo_2826_, v_ik_2827_, v_w_2828_);
lean_dec_ref(v_pivot_2822_);
lean_dec(v_hi_2820_);
lean_dec(v_lo_2819_);
lean_dec(v_n_2818_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2830_, lean_object* v_snd_2831_, lean_object* v_as_2832_, size_t v_i_2833_, size_t v_stop_2834_, lean_object* v_b_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2831_, v_as_2832_, v_i_2833_, v_stop_2834_, v_b_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_snd_2838_, lean_object* v_as_2839_, lean_object* v_i_2840_, lean_object* v_stop_2841_, lean_object* v_b_2842_){
_start:
{
size_t v_i_boxed_2843_; size_t v_stop_boxed_2844_; lean_object* v_res_2845_; 
v_i_boxed_2843_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_stop_boxed_2844_ = lean_unbox_usize(v_stop_2841_);
lean_dec(v_stop_2841_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2837_, v_snd_2838_, v_as_2839_, v_i_boxed_2843_, v_stop_boxed_2844_, v_b_2842_);
lean_dec_ref(v_as_2839_);
lean_dec(v_snd_2838_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v_nextMacroScope_2850_; lean_object* v_ngen_2851_; lean_object* v_auxDeclNGen_2852_; lean_object* v_traceState_2853_; lean_object* v_messages_2854_; lean_object* v_infoState_2855_; lean_object* v_snapshotTasks_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2867_; 
v___x_2849_ = lean_st_ref_take(v___y_2847_);
v_nextMacroScope_2850_ = lean_ctor_get(v___x_2849_, 1);
v_ngen_2851_ = lean_ctor_get(v___x_2849_, 2);
v_auxDeclNGen_2852_ = lean_ctor_get(v___x_2849_, 3);
v_traceState_2853_ = lean_ctor_get(v___x_2849_, 4);
v_messages_2854_ = lean_ctor_get(v___x_2849_, 6);
v_infoState_2855_ = lean_ctor_get(v___x_2849_, 7);
v_snapshotTasks_2856_ = lean_ctor_get(v___x_2849_, 8);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; lean_object* v_unused_2869_; 
v_unused_2868_ = lean_ctor_get(v___x_2849_, 5);
lean_dec(v_unused_2868_);
v_unused_2869_ = lean_ctor_get(v___x_2849_, 0);
lean_dec(v_unused_2869_);
v___x_2858_ = v___x_2849_;
v_isShared_2859_ = v_isSharedCheck_2867_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_snapshotTasks_2856_);
lean_inc(v_infoState_2855_);
lean_inc(v_messages_2854_);
lean_inc(v_traceState_2853_);
lean_inc(v_auxDeclNGen_2852_);
lean_inc(v_ngen_2851_);
lean_inc(v_nextMacroScope_2850_);
lean_dec(v___x_2849_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2867_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 5, v___x_2861_);
lean_ctor_set(v___x_2858_, 0, v_env_2846_);
v___x_2863_ = v___x_2858_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_env_2846_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_nextMacroScope_2850_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_ngen_2851_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_auxDeclNGen_2852_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v_traceState_2853_);
lean_ctor_set(v_reuseFailAlloc_2866_, 5, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2866_, 6, v_messages_2854_);
lean_ctor_set(v_reuseFailAlloc_2866_, 7, v_infoState_2855_);
lean_ctor_set(v_reuseFailAlloc_2866_, 8, v_snapshotTasks_2856_);
v___x_2863_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_st_ref_put(v___y_2847_, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2860_);
return v___x_2865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2870_, v___y_2871_);
lean_dec(v___y_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2874_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2884_, lean_object* v_ext_2885_, lean_object* v_afterSet_2886_, lean_object* v_toAttributeImplCore_2887_, lean_object* v_decl_2888_, lean_object* v_stx_2889_, uint8_t v_kind_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; uint8_t v___x_2948_; uint8_t v___x_2949_; 
v___x_2948_ = 0;
v___x_2949_ = l_Lean_instBEqAttributeKind_beq(v_kind_2890_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v_name_2950_; lean_object* v___x_2951_; 
lean_dec(v_stx_2889_);
lean_dec(v_decl_2888_);
lean_dec_ref(v_afterSet_2886_);
lean_dec_ref(v_ext_2885_);
lean_dec_ref(v_getParam_2884_);
v_name_2950_ = lean_ctor_get(v_toAttributeImplCore_2887_, 1);
lean_inc(v_name_2950_);
lean_dec_ref(v_toAttributeImplCore_2887_);
v___x_2951_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2950_, v_kind_2890_, v___y_2891_, v___y_2892_);
return v___x_2951_;
}
else
{
goto v___jp_2942_;
}
v___jp_2894_:
{
if (v___y_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_dec_ref(v___y_2896_);
v___x_2900_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2895_, v___y_2897_);
return v___x_2900_;
}
else
{
lean_dec_ref(v___y_2895_);
return v___y_2896_;
}
}
v___jp_2901_:
{
lean_object* v___x_2905_; 
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
lean_inc(v_decl_2888_);
v___x_2905_ = lean_apply_5(v_getParam_2884_, v_decl_2888_, v_stx_2889_, v___y_2903_, v___y_2904_, lean_box(0));
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v_toEnvExtension_2908_; lean_object* v_env_2909_; lean_object* v_nextMacroScope_2910_; lean_object* v_ngen_2911_; lean_object* v_auxDeclNGen_2912_; lean_object* v_traceState_2913_; lean_object* v_messages_2914_; lean_object* v_infoState_2915_; lean_object* v_snapshotTasks_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2932_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = lean_st_ref_take(v___y_2904_);
v_toEnvExtension_2908_ = lean_ctor_get(v_ext_2885_, 0);
v_env_2909_ = lean_ctor_get(v___x_2907_, 0);
v_nextMacroScope_2910_ = lean_ctor_get(v___x_2907_, 1);
v_ngen_2911_ = lean_ctor_get(v___x_2907_, 2);
v_auxDeclNGen_2912_ = lean_ctor_get(v___x_2907_, 3);
v_traceState_2913_ = lean_ctor_get(v___x_2907_, 4);
v_messages_2914_ = lean_ctor_get(v___x_2907_, 6);
v_infoState_2915_ = lean_ctor_get(v___x_2907_, 7);
v_snapshotTasks_2916_ = lean_ctor_get(v___x_2907_, 8);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2907_, 5);
lean_dec(v_unused_2933_);
v___x_2918_ = v___x_2907_;
v_isShared_2919_ = v_isSharedCheck_2932_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_snapshotTasks_2916_);
lean_inc(v_infoState_2915_);
lean_inc(v_messages_2914_);
lean_inc(v_traceState_2913_);
lean_inc(v_auxDeclNGen_2912_);
lean_inc(v_ngen_2911_);
lean_inc(v_nextMacroScope_2910_);
lean_inc(v_env_2909_);
lean_dec(v___x_2907_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2932_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v_asyncMode_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
v_asyncMode_2920_ = lean_ctor_get(v_toEnvExtension_2908_, 2);
lean_inc(v_asyncMode_2920_);
lean_inc(v_a_2906_);
lean_inc_n(v_decl_2888_, 2);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v_decl_2888_);
lean_ctor_set(v___x_2921_, 1, v_a_2906_);
v___x_2922_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2885_, v_env_2909_, v___x_2921_, v_asyncMode_2920_, v_decl_2888_);
lean_dec(v_asyncMode_2920_);
v___x_2923_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 5, v___x_2923_);
lean_ctor_set(v___x_2918_, 0, v___x_2922_);
v___x_2925_ = v___x_2918_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2922_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_nextMacroScope_2910_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_ngen_2911_);
lean_ctor_set(v_reuseFailAlloc_2931_, 3, v_auxDeclNGen_2912_);
lean_ctor_set(v_reuseFailAlloc_2931_, 4, v_traceState_2913_);
lean_ctor_set(v_reuseFailAlloc_2931_, 5, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2931_, 6, v_messages_2914_);
lean_ctor_set(v_reuseFailAlloc_2931_, 7, v_infoState_2915_);
lean_ctor_set(v_reuseFailAlloc_2931_, 8, v_snapshotTasks_2916_);
v___x_2925_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_st_ref_put(v___y_2904_, v___x_2925_);
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
v___x_2927_ = lean_apply_5(v_afterSet_2886_, v_decl_2888_, v_a_2906_, v___y_2903_, v___y_2904_, lean_box(0));
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_dec_ref(v___y_2902_);
return v___x_2927_;
}
else
{
lean_object* v_a_2928_; uint8_t v___x_2929_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
v___x_2929_ = l_Lean_Exception_isInterrupt(v_a_2928_);
if (v___x_2929_ == 0)
{
uint8_t v___x_2930_; 
v___x_2930_ = l_Lean_Exception_isRuntime(v_a_2928_);
v___y_2895_ = v___y_2902_;
v___y_2896_ = v___x_2927_;
v___y_2897_ = v___y_2904_;
v___y_2898_ = v___y_2903_;
v___y_2899_ = v___x_2930_;
goto v___jp_2894_;
}
else
{
lean_dec(v_a_2928_);
v___y_2895_ = v___y_2902_;
v___y_2896_ = v___x_2927_;
v___y_2897_ = v___y_2904_;
v___y_2898_ = v___y_2903_;
v___y_2899_ = v___x_2929_;
goto v___jp_2894_;
}
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___y_2902_);
lean_dec(v_decl_2888_);
lean_dec_ref(v_afterSet_2886_);
lean_dec_ref(v_ext_2885_);
v_a_2934_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2905_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2905_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2943_; lean_object* v_env_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_st_ref_get(v___y_2892_);
v_env_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_ref(v_env_2944_);
lean_dec(v___x_2943_);
v___x_2945_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2944_, v_decl_2888_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2887_);
v___y_2902_ = v_env_2944_;
v___y_2903_ = v___y_2891_;
v___y_2904_ = v___y_2892_;
goto v___jp_2901_;
}
else
{
lean_object* v_name_2946_; lean_object* v___x_2947_; 
lean_dec_ref_known(v___x_2945_, 1);
lean_dec_ref(v_env_2944_);
lean_dec(v_stx_2889_);
lean_dec_ref(v_afterSet_2886_);
lean_dec_ref(v_ext_2885_);
lean_dec_ref(v_getParam_2884_);
v_name_2946_ = lean_ctor_get(v_toAttributeImplCore_2887_, 1);
lean_inc(v_name_2946_);
lean_dec_ref(v_toAttributeImplCore_2887_);
v___x_2947_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2946_, v_decl_2888_, v___y_2891_, v___y_2892_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2952_, lean_object* v_ext_2953_, lean_object* v_afterSet_2954_, lean_object* v_toAttributeImplCore_2955_, lean_object* v_decl_2956_, lean_object* v_stx_2957_, lean_object* v_kind_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v_kind_boxed_2962_; lean_object* v_res_2963_; 
v_kind_boxed_2962_ = lean_unbox(v_kind_2958_);
v_res_2963_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2952_, v_ext_2953_, v_afterSet_2954_, v_toAttributeImplCore_2955_, v_decl_2956_, v_stx_2957_, v_kind_boxed_2962_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2964_, lean_object* v_decl_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_name_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_name_2969_ = lean_ctor_get(v_toAttributeImplCore_2964_, 1);
lean_inc(v_name_2969_);
lean_dec_ref(v_toAttributeImplCore_2964_);
v___x_2970_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2971_ = l_Lean_MessageData_ofName(v_name_2969_);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2974_, v___y_2966_, v___y_2967_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2976_, lean_object* v_decl_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2976_, v_decl_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v_decl_2977_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2982_, lean_object* v_ext_2983_){
_start:
{
lean_object* v_toAttributeImplCore_2985_; lean_object* v_getParam_2986_; lean_object* v_afterSet_2987_; uint8_t v_preserveOrder_2988_; lean_object* v___f_2989_; lean_object* v___f_2990_; lean_object* v_attrImpl_2991_; lean_object* v___x_2992_; 
v_toAttributeImplCore_2985_ = lean_ctor_get(v_impl_2982_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2985_, 3);
v_getParam_2986_ = lean_ctor_get(v_impl_2982_, 1);
lean_inc_ref(v_getParam_2986_);
v_afterSet_2987_ = lean_ctor_get(v_impl_2982_, 2);
lean_inc_ref(v_afterSet_2987_);
v_preserveOrder_2988_ = lean_ctor_get_uint8(v_impl_2982_, sizeof(void*)*4);
lean_dec_ref(v_impl_2982_);
lean_inc_ref(v_ext_2983_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2989_, 0, v_getParam_2986_);
lean_closure_set(v___f_2989_, 1, v_ext_2983_);
lean_closure_set(v___f_2989_, 2, v_afterSet_2987_);
lean_closure_set(v___f_2989_, 3, v_toAttributeImplCore_2985_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2990_, 0, v_toAttributeImplCore_2985_);
v_attrImpl_2991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2991_, 0, v_toAttributeImplCore_2985_);
lean_ctor_set(v_attrImpl_2991_, 1, v___f_2989_);
lean_ctor_set(v_attrImpl_2991_, 2, v___f_2990_);
lean_inc_ref(v_attrImpl_2991_);
v___x_2992_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2991_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3000_; 
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v___x_2992_, 0);
lean_dec(v_unused_3001_);
v___x_2994_ = v___x_2992_;
v_isShared_2995_ = v_isSharedCheck_3000_;
goto v_resetjp_2993_;
}
else
{
lean_dec(v___x_2992_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3000_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2996_, 0, v_attrImpl_2991_);
lean_ctor_set(v___x_2996_, 1, v_ext_2983_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*2, v_preserveOrder_2988_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2996_);
v___x_2998_ = v___x_2994_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref_known(v_attrImpl_2991_, 3);
lean_dec_ref(v_ext_2983_);
v_a_3002_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2992_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2992_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3010_, lean_object* v_ext_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3010_, v_ext_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3014_, lean_object* v_impl_3015_, lean_object* v_ext_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3015_, v_ext_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3019_, lean_object* v_impl_3020_, lean_object* v_ext_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3019_, v_impl_3020_, v_ext_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3024_){
_start:
{
lean_object* v_toAttributeImplCore_3026_; uint8_t v_preserveOrder_3027_; lean_object* v_filterExport_3028_; lean_object* v_ref_3029_; lean_object* v___x_3030_; 
v_toAttributeImplCore_3026_ = lean_ctor_get(v_impl_3024_, 0);
v_preserveOrder_3027_ = lean_ctor_get_uint8(v_impl_3024_, sizeof(void*)*4);
v_filterExport_3028_ = lean_ctor_get(v_impl_3024_, 3);
v_ref_3029_ = lean_ctor_get(v_toAttributeImplCore_3026_, 0);
lean_inc_ref(v_filterExport_3028_);
lean_inc(v_ref_3029_);
v___x_3030_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3029_, v_preserveOrder_3027_, v_filterExport_3028_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3024_, v_a_3031_);
return v___x_3032_;
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v_impl_3024_);
v_a_3033_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3030_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3030_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_registerParametricAttribute___redArg(v_impl_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3044_, lean_object* v_impl_3045_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_registerParametricAttribute___redArg(v_impl_3045_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3048_, lean_object* v_impl_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_registerParametricAttribute(v_00_u03b1_3048_, v_impl_3049_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3052_, lean_object* v___x_3053_, lean_object* v___x_3054_, lean_object* v_a_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_fst_3058_; uint8_t v___x_3059_; 
v_fst_3058_ = lean_ctor_get(v_a_3055_, 0);
v___x_3059_ = lean_name_eq(v_fst_3058_, v_decl_3052_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
lean_dec_ref(v_a_3055_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3053_);
return v___x_3060_;
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref(v___x_3053_);
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_a_3055_);
v___x_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v___x_3054_);
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3065_, lean_object* v___x_3066_, lean_object* v___x_3067_, lean_object* v_a_3068_, lean_object* v_x_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3065_, v___x_3066_, v___x_3067_, v_a_3068_, v_x_3069_, v___y_3070_);
lean_dec_ref(v___y_3070_);
lean_dec(v_decl_3065_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3099_, lean_object* v_ext_3100_, uint8_t v_preserveOrder_3101_, lean_object* v_env_3102_, lean_object* v_decl_3103_){
_start:
{
lean_object* v___y_3105_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3117_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3102_, v_decl_3103_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_toEnvExtension_3118_; lean_object* v_asyncMode_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v_snd_3122_; lean_object* v___x_3123_; 
lean_dec(v_inst_3099_);
v_toEnvExtension_3118_ = lean_ctor_get(v_ext_3100_, 0);
v_asyncMode_3119_ = lean_ctor_get(v_toEnvExtension_3118_, 2);
v___x_3120_ = lean_box(0);
v___x_3121_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3116_, v_ext_3100_, v_env_3102_, v_asyncMode_3119_, v___x_3120_);
v_snd_3122_ = lean_ctor_get(v___x_3121_, 1);
lean_inc(v_snd_3122_);
lean_dec(v___x_3121_);
v___x_3123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3122_, v_decl_3103_);
lean_dec(v_decl_3103_);
lean_dec(v_snd_3122_);
return v___x_3123_;
}
else
{
if (v_preserveOrder_3101_ == 0)
{
lean_object* v_val_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_val_3124_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_val_3124_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3125_ = 0;
v___x_3126_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3116_, v_ext_3100_, v_env_3102_, v_val_3124_, v___x_3125_);
lean_dec(v_val_3124_);
lean_dec_ref(v_env_3102_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_array_get_size(v___x_3126_);
v___x_3129_ = lean_nat_dec_lt(v___x_3127_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref(v___x_3126_);
lean_dec(v_decl_3103_);
lean_dec(v_inst_3099_);
v___x_3130_ = lean_box(0);
return v___x_3130_;
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = lean_unsigned_to_nat(1u);
v___x_3132_ = lean_nat_sub(v___x_3128_, v___x_3131_);
v___x_3133_ = lean_nat_dec_le(v___x_3127_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_dec(v___x_3132_);
lean_dec_ref(v___x_3126_);
lean_dec(v_decl_3103_);
lean_dec(v_inst_3099_);
v___x_3134_ = lean_box(0);
return v___x_3134_;
}
else
{
lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___f_3135_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v_decl_3103_);
lean_ctor_set(v___x_3136_, 1, v_inst_3099_);
v___x_3137_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3138_ = l_Array_binSearchAux___redArg(v___f_3135_, v___x_3137_, v___x_3126_, v___x_3136_, v___x_3127_, v___x_3132_);
lean_dec_ref(v___x_3126_);
v___y_3105_ = v___x_3138_;
goto v___jp_3104_;
}
}
}
else
{
lean_object* v_val_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___f_3146_; size_t v_sz_3147_; size_t v___x_3148_; lean_object* v___x_3149_; lean_object* v_fst_3150_; 
lean_dec(v_inst_3099_);
v_val_3139_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3140_ = 0;
v___x_3141_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3116_, v_ext_3100_, v_env_3102_, v_val_3139_, v___x_3140_);
lean_dec(v_val_3139_);
lean_dec_ref(v_env_3102_);
v___x_3142_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_box(0);
v___x_3145_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3146_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3146_, 0, v_decl_3103_);
lean_closure_set(v___f_3146_, 1, v___x_3145_);
lean_closure_set(v___f_3146_, 2, v___x_3144_);
v_sz_3147_ = lean_array_size(v___x_3141_);
v___x_3148_ = ((size_t)0ULL);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3142_, v___x_3141_, v___f_3146_, v_sz_3147_, v___x_3148_, v___x_3145_);
v_fst_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_fst_3150_);
lean_dec(v___x_3149_);
if (lean_obj_tag(v_fst_3150_) == 0)
{
return v___x_3143_;
}
else
{
lean_object* v_val_3151_; 
v_val_3151_ = lean_ctor_get(v_fst_3150_, 0);
lean_inc(v_val_3151_);
lean_dec_ref_known(v_fst_3150_, 1);
v___y_3105_ = v_val_3151_;
goto v___jp_3104_;
}
}
}
v___jp_3104_:
{
if (lean_obj_tag(v___y_3105_) == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_box(0);
return v___x_3106_;
}
else
{
lean_object* v_val_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3115_; 
v_val_3107_ = lean_ctor_get(v___y_3105_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___y_3105_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3109_ = v___y_3105_;
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_val_3107_);
lean_dec(v___y_3105_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_snd_3111_; lean_object* v___x_3113_; 
v_snd_3111_ = lean_ctor_get(v_val_3107_, 1);
lean_inc(v_snd_3111_);
lean_dec(v_val_3107_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v_snd_3111_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_snd_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3152_, lean_object* v_ext_3153_, lean_object* v_preserveOrder_3154_, lean_object* v_env_3155_, lean_object* v_decl_3156_){
_start:
{
uint8_t v_preserveOrder_boxed_3157_; lean_object* v_res_3158_; 
v_preserveOrder_boxed_3157_ = lean_unbox(v_preserveOrder_3154_);
v_res_3158_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3152_, v_ext_3153_, v_preserveOrder_boxed_3157_, v_env_3155_, v_decl_3156_);
lean_dec_ref(v_ext_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3159_, lean_object* v_inst_3160_, lean_object* v_ext_3161_, uint8_t v_preserveOrder_3162_, lean_object* v_env_3163_, lean_object* v_decl_3164_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3160_, v_ext_3161_, v_preserveOrder_3162_, v_env_3163_, v_decl_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_inst_3167_, lean_object* v_ext_3168_, lean_object* v_preserveOrder_3169_, lean_object* v_env_3170_, lean_object* v_decl_3171_){
_start:
{
uint8_t v_preserveOrder_boxed_3172_; lean_object* v_res_3173_; 
v_preserveOrder_boxed_3172_ = lean_unbox(v_preserveOrder_3169_);
v_res_3173_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3166_, v_inst_3167_, v_ext_3168_, v_preserveOrder_boxed_3172_, v_env_3170_, v_decl_3171_);
lean_dec_ref(v_ext_3168_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3174_, lean_object* v_attr_3175_, lean_object* v_env_3176_, lean_object* v_decl_3177_){
_start:
{
lean_object* v_ext_3178_; uint8_t v_preserveOrder_3179_; lean_object* v___x_3180_; 
v_ext_3178_ = lean_ctor_get(v_attr_3175_, 1);
v_preserveOrder_3179_ = lean_ctor_get_uint8(v_attr_3175_, sizeof(void*)*2);
v___x_3180_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3174_, v_ext_3178_, v_preserveOrder_3179_, v_env_3176_, v_decl_3177_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3181_, lean_object* v_attr_3182_, lean_object* v_env_3183_, lean_object* v_decl_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3181_, v_attr_3182_, v_env_3183_, v_decl_3184_);
lean_dec_ref(v_attr_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3186_, lean_object* v_inst_3187_, lean_object* v_attr_3188_, lean_object* v_env_3189_, lean_object* v_decl_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3187_, v_attr_3188_, v_env_3189_, v_decl_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_inst_3193_, lean_object* v_attr_3194_, lean_object* v_env_3195_, lean_object* v_decl_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3192_, v_inst_3193_, v_attr_3194_, v_env_3195_, v_decl_3196_);
lean_dec_ref(v_attr_3194_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3202_, lean_object* v_attr_3203_, lean_object* v_env_3204_, lean_object* v_decl_3205_, lean_object* v_param_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3204_, v_decl_3205_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_toEnvExtension_3208_; lean_object* v_asyncMode_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_snd_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3243_; 
v_toEnvExtension_3208_ = lean_ctor_get(v_ext_3202_, 0);
v_asyncMode_3209_ = lean_ctor_get(v_toEnvExtension_3208_, 2);
lean_inc(v_asyncMode_3209_);
v___x_3210_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3211_ = lean_box(0);
lean_inc_ref(v_env_3204_);
v___x_3212_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3210_, v_ext_3202_, v_env_3204_, v_asyncMode_3209_, v___x_3211_);
v_snd_3213_ = lean_ctor_get(v___x_3212_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v___x_3212_, 0);
lean_dec(v_unused_3244_);
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3243_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_snd_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3243_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3213_, v_decl_3205_);
lean_dec(v_snd_3213_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3219_; 
lean_dec_ref(v_attr_3203_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 1, v_param_3206_);
lean_ctor_set(v___x_3215_, 0, v_decl_3205_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_decl_3205_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_param_3206_);
v___x_3219_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3202_, v_env_3204_, v___x_3219_, v_asyncMode_3209_, v___x_3211_);
lean_dec(v_asyncMode_3209_);
v___x_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
}
else
{
lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3241_; 
lean_del_object(v___x_3215_);
lean_dec(v_asyncMode_3209_);
lean_dec(v_param_3206_);
lean_dec_ref(v_env_3204_);
lean_dec_ref(v_ext_3202_);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v___x_3217_, 0);
lean_dec(v_unused_3242_);
v___x_3224_ = v___x_3217_;
v_isShared_3225_ = v_isSharedCheck_3241_;
goto v_resetjp_3223_;
}
else
{
lean_dec(v___x_3217_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3241_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v_toAttributeImplCore_3226_; lean_object* v_name_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
v_toAttributeImplCore_3226_ = lean_ctor_get(v_attr_3203_, 0);
lean_inc_ref(v_toAttributeImplCore_3226_);
lean_dec_ref(v_attr_3203_);
v_name_3227_ = lean_ctor_get(v_toAttributeImplCore_3226_, 1);
lean_inc(v_name_3227_);
lean_dec_ref(v_toAttributeImplCore_3226_);
v___x_3228_ = 1;
v___x_3229_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3230_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3227_, v___x_3228_);
v___x_3231_ = lean_string_append(v___x_3229_, v___x_3230_);
lean_dec_ref(v___x_3230_);
v___x_3232_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3233_ = lean_string_append(v___x_3231_, v___x_3232_);
v___x_3234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3205_, v___x_3228_);
v___x_3235_ = lean_string_append(v___x_3233_, v___x_3234_);
lean_dec_ref(v___x_3234_);
v___x_3236_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3237_ = lean_string_append(v___x_3235_, v___x_3236_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3237_);
v___x_3239_ = v___x_3224_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
else
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_param_3206_);
lean_dec_ref(v_env_3204_);
lean_dec_ref(v_ext_3202_);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; 
v_unused_3264_ = lean_ctor_get(v___x_3207_, 0);
lean_dec(v_unused_3264_);
v___x_3246_ = v___x_3207_;
v_isShared_3247_ = v_isSharedCheck_3263_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v___x_3207_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3263_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_toAttributeImplCore_3248_; lean_object* v_name_3249_; uint8_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v_toAttributeImplCore_3248_ = lean_ctor_get(v_attr_3203_, 0);
lean_inc_ref(v_toAttributeImplCore_3248_);
lean_dec_ref(v_attr_3203_);
v_name_3249_ = lean_ctor_get(v_toAttributeImplCore_3248_, 1);
lean_inc(v_name_3249_);
lean_dec_ref(v_toAttributeImplCore_3248_);
v___x_3250_ = 1;
v___x_3251_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3249_, v___x_3250_);
v___x_3253_ = lean_string_append(v___x_3251_, v___x_3252_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3255_ = lean_string_append(v___x_3253_, v___x_3254_);
v___x_3256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3205_, v___x_3250_);
v___x_3257_ = lean_string_append(v___x_3255_, v___x_3256_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3259_ = lean_string_append(v___x_3257_, v___x_3258_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3259_);
v___x_3261_ = v___x_3246_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3265_, lean_object* v_ext_3266_, lean_object* v_attr_3267_, lean_object* v_env_3268_, lean_object* v_decl_3269_, lean_object* v_param_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3266_, v_attr_3267_, v_env_3268_, v_decl_3269_, v_param_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3272_, lean_object* v_env_3273_, lean_object* v_decl_3274_, lean_object* v_param_3275_){
_start:
{
lean_object* v_attr_3276_; lean_object* v_ext_3277_; lean_object* v___x_3278_; 
v_attr_3276_ = lean_ctor_get(v_attr_3272_, 0);
lean_inc_ref(v_attr_3276_);
v_ext_3277_ = lean_ctor_get(v_attr_3272_, 1);
lean_inc_ref(v_ext_3277_);
lean_dec_ref(v_attr_3272_);
v___x_3278_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3277_, v_attr_3276_, v_env_3273_, v_decl_3274_, v_param_3275_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3279_, lean_object* v_attr_3280_, lean_object* v_env_3281_, lean_object* v_decl_3282_, lean_object* v_param_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3280_, v_env_3281_, v_decl_3282_, v_param_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3290_, v___y_3291_);
lean_dec_ref(v___y_3291_);
lean_dec_ref(v_x_3290_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3294_, lean_object* v_x_3295_){
_start:
{
lean_inc(v_s_3294_);
return v_s_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3296_, v_x_3297_);
lean_dec_ref(v_x_3297_);
lean_dec(v_s_3296_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3302_, lean_object* v_x_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3302_, v_x_3303_);
lean_dec(v_x_3303_);
lean_dec_ref(v_x_3302_);
return v_res_3304_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___f_3308_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3309_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3310_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3311_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3314_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v___x_3312_);
lean_ctor_set(v___x_3314_, 2, v___f_3311_);
lean_ctor_set(v___x_3314_, 3, v___f_3310_);
lean_ctor_set(v___x_3314_, 4, v___f_3309_);
lean_ctor_set(v___x_3314_, 5, v___f_3308_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3316_ = lean_box(0);
v___x_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3321_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3334_);
lean_dec(v_x_3334_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_){
_start:
{
if (lean_obj_tag(v_x_3338_) == 0)
{
return v_x_3337_;
}
else
{
lean_object* v_head_3339_; lean_object* v_tail_3340_; lean_object* v___x_3341_; 
v_head_3339_ = lean_ctor_get(v_x_3338_, 0);
lean_inc(v_head_3339_);
v_tail_3340_ = lean_ctor_get(v_x_3338_, 1);
lean_inc(v_tail_3340_);
lean_dec_ref_known(v_x_3338_, 2);
v___x_3341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3336_, v_head_3339_);
if (lean_obj_tag(v___x_3341_) == 1)
{
lean_object* v_val_3342_; lean_object* v___x_3343_; 
v_val_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3339_, v_val_3342_, v_x_3337_);
v_x_3337_ = v___x_3343_;
v_x_3338_ = v_tail_3340_;
goto _start;
}
else
{
lean_dec(v___x_3341_);
lean_dec(v_head_3339_);
v_x_3338_ = v_tail_3340_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3346_, v_x_3347_, v_x_3348_);
lean_dec(v_newState_3346_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3350_, lean_object* v_newState_3351_, lean_object* v_consts_3352_, lean_object* v_st_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3351_, v_st_3353_, v_consts_3352_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3355_, lean_object* v_newState_3356_, lean_object* v_consts_3357_, lean_object* v_st_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3355_, v_newState_3356_, v_consts_3357_, v_st_3358_);
lean_dec(v_newState_3356_);
lean_dec(v_x_3355_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3369_){
_start:
{
lean_object* v___x_3370_; lean_object* v___y_3372_; 
v___x_3370_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3369_) == 0)
{
lean_object* v_size_3376_; 
v_size_3376_ = lean_ctor_get(v_s_3369_, 0);
lean_inc(v_size_3376_);
lean_dec_ref_known(v_s_3369_, 5);
v___y_3372_ = v_size_3376_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___y_3372_ = v___x_3377_;
goto v___jp_3371_;
}
v___jp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = l_Nat_reprFast(v___y_3372_);
v___x_3374_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3370_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3378_, lean_object* v_as_3379_, size_t v_i_3380_, size_t v_stop_3381_, lean_object* v_b_3382_){
_start:
{
lean_object* v___y_3384_; uint8_t v___x_3388_; 
v___x_3388_ = lean_usize_dec_eq(v_i_3380_, v_stop_3381_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v_fst_3390_; uint8_t v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3389_ = lean_array_uget_borrowed(v_as_3379_, v_i_3380_);
v_fst_3390_ = lean_ctor_get(v___x_3389_, 0);
v___x_3391_ = 1;
lean_inc_ref(v_env_3378_);
v___x_3392_ = l_Lean_Environment_setExporting(v_env_3378_, v___x_3391_);
lean_inc(v_fst_3390_);
v___x_3393_ = l_Lean_Environment_contains(v___x_3392_, v_fst_3390_, v___x_3388_);
if (v___x_3393_ == 0)
{
v___y_3384_ = v_b_3382_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3394_; 
lean_inc(v___x_3389_);
v___x_3394_ = lean_array_push(v_b_3382_, v___x_3389_);
v___y_3384_ = v___x_3394_;
goto v___jp_3383_;
}
}
else
{
lean_dec_ref(v_env_3378_);
return v_b_3382_;
}
v___jp_3383_:
{
size_t v___x_3385_; size_t v___x_3386_; 
v___x_3385_ = ((size_t)1ULL);
v___x_3386_ = lean_usize_add(v_i_3380_, v___x_3385_);
v_i_3380_ = v___x_3386_;
v_b_3382_ = v___y_3384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3395_, lean_object* v_as_3396_, lean_object* v_i_3397_, lean_object* v_stop_3398_, lean_object* v_b_3399_){
_start:
{
size_t v_i_boxed_3400_; size_t v_stop_boxed_3401_; lean_object* v_res_3402_; 
v_i_boxed_3400_ = lean_unbox_usize(v_i_3397_);
lean_dec(v_i_3397_);
v_stop_boxed_3401_ = lean_unbox_usize(v_stop_3398_);
lean_dec(v_stop_3398_);
v_res_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3395_, v_as_3396_, v_i_boxed_3400_, v_stop_boxed_3401_, v_b_3399_);
lean_dec_ref(v_as_3396_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3403_, lean_object* v_m_3404_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___y_3408_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___y_3425_; lean_object* v___y_3426_; uint8_t v___x_3428_; 
v___x_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3422_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3406_, v_m_3404_);
v___x_3423_ = lean_array_get_size(v___x_3422_);
v___x_3428_ = lean_nat_dec_eq(v___x_3423_, v___x_3405_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___y_3432_; uint8_t v___x_3434_; 
v___x_3429_ = lean_unsigned_to_nat(1u);
v___x_3430_ = lean_nat_sub(v___x_3423_, v___x_3429_);
v___x_3434_ = lean_nat_dec_le(v___x_3405_, v___x_3430_);
if (v___x_3434_ == 0)
{
lean_inc(v___x_3430_);
v___y_3432_ = v___x_3430_;
goto v___jp_3431_;
}
else
{
v___y_3432_ = v___x_3405_;
goto v___jp_3431_;
}
v___jp_3431_:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_nat_dec_le(v___y_3432_, v___x_3430_);
if (v___x_3433_ == 0)
{
lean_dec(v___x_3430_);
lean_inc(v___y_3432_);
v___y_3425_ = v___y_3432_;
v___y_3426_ = v___y_3432_;
goto v___jp_3424_;
}
else
{
v___y_3425_ = v___y_3432_;
v___y_3426_ = v___x_3430_;
goto v___jp_3424_;
}
}
}
else
{
v___y_3408_ = v___x_3422_;
goto v___jp_3407_;
}
v___jp_3407_:
{
lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3409_ = lean_array_get_size(v___y_3408_);
v___x_3410_ = lean_nat_dec_lt(v___x_3405_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_dec_ref(v_env_3403_);
v___x_3411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3406_);
lean_ctor_set(v___x_3411_, 1, v___x_3406_);
lean_ctor_set(v___x_3411_, 2, v___y_3408_);
return v___x_3411_;
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_nat_dec_le(v___x_3409_, v___x_3409_);
if (v___x_3412_ == 0)
{
if (v___x_3410_ == 0)
{
lean_object* v___x_3413_; 
lean_dec_ref(v_env_3403_);
v___x_3413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3406_);
lean_ctor_set(v___x_3413_, 1, v___x_3406_);
lean_ctor_set(v___x_3413_, 2, v___y_3408_);
return v___x_3413_;
}
else
{
size_t v___x_3414_; size_t v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3414_ = ((size_t)0ULL);
v___x_3415_ = lean_usize_of_nat(v___x_3409_);
v___x_3416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3403_, v___y_3408_, v___x_3414_, v___x_3415_, v___x_3406_);
lean_inc_ref(v___x_3416_);
v___x_3417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
lean_ctor_set(v___x_3417_, 2, v___y_3408_);
return v___x_3417_;
}
}
else
{
size_t v___x_3418_; size_t v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3418_ = ((size_t)0ULL);
v___x_3419_ = lean_usize_of_nat(v___x_3409_);
v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3403_, v___y_3408_, v___x_3418_, v___x_3419_, v___x_3406_);
lean_inc_ref(v___x_3420_);
v___x_3421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
lean_ctor_set(v___x_3421_, 2, v___y_3408_);
return v___x_3421_;
}
}
}
v___jp_3424_:
{
lean_object* v___x_3427_; 
v___x_3427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3423_, v___x_3422_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
v___y_3408_ = v___x_3427_;
goto v___jp_3407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3435_, lean_object* v_m_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3435_, v_m_3436_);
lean_dec(v_m_3436_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3438_, lean_object* v_p_3439_){
_start:
{
lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3442_; 
v_fst_3440_ = lean_ctor_get(v_p_3439_, 0);
lean_inc(v_fst_3440_);
v_snd_3441_ = lean_ctor_get(v_p_3439_, 1);
lean_inc(v_snd_3441_);
lean_dec_ref(v_p_3439_);
v___x_3442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3440_, v_snd_3441_, v_s_3438_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3443_, lean_object* v_x_3444_, lean_object* v_x_3445_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3443_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3448_, v_x_3449_, v_x_3450_);
lean_dec_ref(v_x_3450_);
lean_dec_ref(v_x_3449_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3453_){
_start:
{
if (lean_obj_tag(v_as_3453_) == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
return v___x_3456_;
}
else
{
lean_object* v_head_3457_; lean_object* v_tail_3458_; lean_object* v___x_3459_; 
v_head_3457_ = lean_ctor_get(v_as_3453_, 0);
lean_inc(v_head_3457_);
v_tail_3458_ = lean_ctor_get(v_as_3453_, 1);
lean_inc(v_tail_3458_);
lean_dec_ref_known(v_as_3453_, 2);
v___x_3459_ = l_Lean_registerBuiltinAttribute(v_head_3457_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_dec_ref_known(v___x_3459_, 1);
v_as_3453_ = v_tail_3458_;
goto _start;
}
else
{
lean_dec(v_tail_3458_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3464_, lean_object* v_snd_3465_, lean_object* v_a_3466_, lean_object* v_fst_3467_, lean_object* v_decl_3468_, lean_object* v_stx_3469_, uint8_t v_kind_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3469_, v___y_3471_, v___y_3472_);
if (lean_obj_tag(v___x_3515_) == 0)
{
uint8_t v___x_3516_; uint8_t v___x_3517_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = 0;
v___x_3517_ = l_Lean_instBEqAttributeKind_beq(v_kind_3470_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
lean_dec(v_decl_3468_);
lean_dec_ref(v_a_3466_);
lean_dec(v_snd_3465_);
lean_dec_ref(v_validate_3464_);
v___x_3518_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3467_, v_kind_3470_, v___y_3471_, v___y_3472_);
return v___x_3518_;
}
else
{
goto v___jp_3510_;
}
}
else
{
lean_dec(v_decl_3468_);
lean_dec(v_fst_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_snd_3465_);
lean_dec_ref(v_validate_3464_);
return v___x_3515_;
}
v___jp_3474_:
{
lean_object* v___x_3477_; 
lean_inc(v___y_3476_);
lean_inc_ref(v___y_3475_);
lean_inc(v_snd_3465_);
lean_inc(v_decl_3468_);
v___x_3477_ = lean_apply_5(v_validate_3464_, v_decl_3468_, v_snd_3465_, v___y_3475_, v___y_3476_, lean_box(0));
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3508_; 
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3508_ == 0)
{
lean_object* v_unused_3509_; 
v_unused_3509_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3509_);
v___x_3479_ = v___x_3477_;
v_isShared_3480_ = v_isSharedCheck_3508_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3477_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3508_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v_toEnvExtension_3482_; lean_object* v_env_3483_; lean_object* v_nextMacroScope_3484_; lean_object* v_ngen_3485_; lean_object* v_auxDeclNGen_3486_; lean_object* v_traceState_3487_; lean_object* v_messages_3488_; lean_object* v_infoState_3489_; lean_object* v_snapshotTasks_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3506_; 
v___x_3481_ = lean_st_ref_take(v___y_3476_);
v_toEnvExtension_3482_ = lean_ctor_get(v_a_3466_, 0);
v_env_3483_ = lean_ctor_get(v___x_3481_, 0);
v_nextMacroScope_3484_ = lean_ctor_get(v___x_3481_, 1);
v_ngen_3485_ = lean_ctor_get(v___x_3481_, 2);
v_auxDeclNGen_3486_ = lean_ctor_get(v___x_3481_, 3);
v_traceState_3487_ = lean_ctor_get(v___x_3481_, 4);
v_messages_3488_ = lean_ctor_get(v___x_3481_, 6);
v_infoState_3489_ = lean_ctor_get(v___x_3481_, 7);
v_snapshotTasks_3490_ = lean_ctor_get(v___x_3481_, 8);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v___x_3481_, 5);
lean_dec(v_unused_3507_);
v___x_3492_ = v___x_3481_;
v_isShared_3493_ = v_isSharedCheck_3506_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snapshotTasks_3490_);
lean_inc(v_infoState_3489_);
lean_inc(v_messages_3488_);
lean_inc(v_traceState_3487_);
lean_inc(v_auxDeclNGen_3486_);
lean_inc(v_ngen_3485_);
lean_inc(v_nextMacroScope_3484_);
lean_inc(v_env_3483_);
lean_dec(v___x_3481_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3506_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_asyncMode_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v_asyncMode_3494_ = lean_ctor_get(v_toEnvExtension_3482_, 2);
lean_inc(v_asyncMode_3494_);
v___x_3495_ = lean_box(0);
lean_inc(v_decl_3468_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v_decl_3468_);
lean_ctor_set(v___x_3496_, 1, v_snd_3465_);
v___x_3497_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3466_, v_env_3483_, v___x_3496_, v_asyncMode_3494_, v_decl_3468_);
lean_dec(v_asyncMode_3494_);
v___x_3498_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 5, v___x_3498_);
lean_ctor_set(v___x_3492_, 0, v___x_3497_);
v___x_3500_ = v___x_3492_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_nextMacroScope_3484_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_ngen_3485_);
lean_ctor_set(v_reuseFailAlloc_3505_, 3, v_auxDeclNGen_3486_);
lean_ctor_set(v_reuseFailAlloc_3505_, 4, v_traceState_3487_);
lean_ctor_set(v_reuseFailAlloc_3505_, 5, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3505_, 6, v_messages_3488_);
lean_ctor_set(v_reuseFailAlloc_3505_, 7, v_infoState_3489_);
lean_ctor_set(v_reuseFailAlloc_3505_, 8, v_snapshotTasks_3490_);
v___x_3500_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3501_ = lean_st_ref_put(v___y_3476_, v___x_3500_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3495_);
v___x_3503_ = v___x_3479_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3495_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
else
{
lean_dec(v_decl_3468_);
lean_dec_ref(v_a_3466_);
lean_dec(v_snd_3465_);
return v___x_3477_;
}
}
v___jp_3510_:
{
lean_object* v___x_3511_; lean_object* v_env_3512_; lean_object* v___x_3513_; 
v___x_3511_ = lean_st_ref_get(v___y_3472_);
v_env_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc_ref(v_env_3512_);
lean_dec(v___x_3511_);
v___x_3513_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3512_, v_decl_3468_);
lean_dec_ref(v_env_3512_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_dec(v_fst_3467_);
v___y_3475_ = v___y_3471_;
v___y_3476_ = v___y_3472_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3514_; 
lean_dec_ref_known(v___x_3513_, 1);
lean_dec_ref(v_a_3466_);
lean_dec(v_snd_3465_);
lean_dec_ref(v_validate_3464_);
v___x_3514_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3467_, v_decl_3468_, v___y_3471_, v___y_3472_);
return v___x_3514_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3519_, lean_object* v_snd_3520_, lean_object* v_a_3521_, lean_object* v_fst_3522_, lean_object* v_decl_3523_, lean_object* v_stx_3524_, lean_object* v_kind_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
uint8_t v_kind_boxed_3529_; lean_object* v_res_3530_; 
v_kind_boxed_3529_ = lean_unbox(v_kind_3525_);
v_res_3530_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3519_, v_snd_3520_, v_a_3521_, v_fst_3522_, v_decl_3523_, v_stx_3524_, v_kind_boxed_3529_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3531_, lean_object* v_decl_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3536_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3537_ = l_Lean_MessageData_ofName(v_fst_3531_);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3538_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3540_, v___y_3533_, v___y_3534_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3542_, lean_object* v_decl_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3542_, v_decl_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v_decl_3543_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3548_, lean_object* v_a_3549_, lean_object* v_ref_3550_, uint8_t v_applicationTime_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
if (lean_obj_tag(v_a_3552_) == 0)
{
lean_object* v___x_3554_; 
lean_dec(v_ref_3550_);
lean_dec_ref(v_a_3549_);
lean_dec_ref(v_validate_3548_);
v___x_3554_ = l_List_reverse___redArg(v_a_3553_);
return v___x_3554_;
}
else
{
lean_object* v_head_3555_; lean_object* v_snd_3556_; lean_object* v_tail_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3572_; 
v_head_3555_ = lean_ctor_get(v_a_3552_, 0);
lean_inc(v_head_3555_);
v_snd_3556_ = lean_ctor_get(v_head_3555_, 1);
lean_inc(v_snd_3556_);
v_tail_3557_ = lean_ctor_get(v_a_3552_, 1);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3552_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_a_3552_, 0);
lean_dec(v_unused_3573_);
v___x_3559_ = v_a_3552_;
v_isShared_3560_ = v_isSharedCheck_3572_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_tail_3557_);
lean_dec(v_a_3552_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3572_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v_fst_3561_; lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v_fst_3561_ = lean_ctor_get(v_head_3555_, 0);
lean_inc_n(v_fst_3561_, 3);
lean_dec(v_head_3555_);
v_fst_3562_ = lean_ctor_get(v_snd_3556_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_snd_3556_, 1);
lean_inc(v_snd_3563_);
lean_dec(v_snd_3556_);
v___f_3564_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3564_, 0, v_fst_3561_);
lean_inc_ref(v_a_3549_);
lean_inc_ref(v_validate_3548_);
v___f_3565_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3565_, 0, v_validate_3548_);
lean_closure_set(v___f_3565_, 1, v_snd_3563_);
lean_closure_set(v___f_3565_, 2, v_a_3549_);
lean_closure_set(v___f_3565_, 3, v_fst_3561_);
lean_inc(v_ref_3550_);
v___x_3566_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3566_, 0, v_ref_3550_);
lean_ctor_set(v___x_3566_, 1, v_fst_3561_);
lean_ctor_set(v___x_3566_, 2, v_fst_3562_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*3, v_applicationTime_3551_);
v___x_3567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
lean_ctor_set(v___x_3567_, 1, v___f_3565_);
lean_ctor_set(v___x_3567_, 2, v___f_3564_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 1, v_a_3553_);
lean_ctor_set(v___x_3559_, 0, v___x_3567_);
v___x_3569_ = v___x_3559_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_a_3553_);
v___x_3569_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
v_a_3552_ = v_tail_3557_;
v_a_3553_ = v___x_3569_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3574_, lean_object* v_a_3575_, lean_object* v_ref_3576_, lean_object* v_applicationTime_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
uint8_t v_applicationTime_boxed_3580_; lean_object* v_res_3581_; 
v_applicationTime_boxed_3580_ = lean_unbox(v_applicationTime_3577_);
v_res_3581_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3574_, v_a_3575_, v_ref_3576_, v_applicationTime_boxed_3580_, v_a_3578_, v_a_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3595_, lean_object* v_validate_3596_, uint8_t v_applicationTime_3597_, lean_object* v_ref_3598_){
_start:
{
lean_object* v___f_3600_; lean_object* v___f_3601_; lean_object* v___f_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___f_3600_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3601_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3602_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3603_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3604_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3605_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3606_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3607_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3598_);
v___x_3608_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3608_, 0, v_ref_3598_);
lean_ctor_set(v___x_3608_, 1, v___f_3604_);
lean_ctor_set(v___x_3608_, 2, v___f_3605_);
lean_ctor_set(v___x_3608_, 3, v___f_3603_);
lean_ctor_set(v___x_3608_, 4, v___f_3602_);
lean_ctor_set(v___x_3608_, 5, v___f_3601_);
lean_ctor_set(v___x_3608_, 6, v___x_3606_);
lean_ctor_set(v___x_3608_, 7, v___x_3607_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set(v___x_3609_, 1, v___f_3600_);
v___x_3610_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3609_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc_n(v_a_3611_, 2);
lean_dec_ref_known(v___x_3610_, 1);
v___x_3612_ = lean_box(0);
v___x_3613_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3596_, v_a_3611_, v_ref_3598_, v_applicationTime_3597_, v_attrDescrs_3595_, v___x_3612_);
lean_inc(v___x_3613_);
v___x_3614_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3613_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3622_; 
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v___x_3614_, 0);
lean_dec(v_unused_3623_);
v___x_3616_ = v___x_3614_;
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
else
{
lean_dec(v___x_3614_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3613_);
lean_ctor_set(v___x_3618_, 1, v_a_3611_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3618_);
v___x_3620_ = v___x_3616_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v___x_3613_);
lean_dec(v_a_3611_);
v_a_3624_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3614_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3614_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_ref_3598_);
lean_dec_ref(v_validate_3596_);
lean_dec(v_attrDescrs_3595_);
v_a_3632_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3610_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3610_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3640_, lean_object* v_validate_3641_, lean_object* v_applicationTime_3642_, lean_object* v_ref_3643_, lean_object* v_a_3644_){
_start:
{
uint8_t v_applicationTime_boxed_3645_; lean_object* v_res_3646_; 
v_applicationTime_boxed_3645_ = lean_unbox(v_applicationTime_3642_);
v_res_3646_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3640_, v_validate_3641_, v_applicationTime_boxed_3645_, v_ref_3643_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3647_, lean_object* v_attrDescrs_3648_, lean_object* v_validate_3649_, uint8_t v_applicationTime_3650_, lean_object* v_ref_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3648_, v_validate_3649_, v_applicationTime_3650_, v_ref_3651_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3654_, lean_object* v_attrDescrs_3655_, lean_object* v_validate_3656_, lean_object* v_applicationTime_3657_, lean_object* v_ref_3658_, lean_object* v_a_3659_){
_start:
{
uint8_t v_applicationTime_boxed_3660_; lean_object* v_res_3661_; 
v_applicationTime_boxed_3660_ = lean_unbox(v_applicationTime_3657_);
v_res_3661_ = l_Lean_registerEnumAttributes(v_00_u03b1_3654_, v_attrDescrs_3655_, v_validate_3656_, v_applicationTime_boxed_3660_, v_ref_3658_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3662_, lean_object* v_env_3663_, lean_object* v_as_3664_, size_t v_i_3665_, size_t v_stop_3666_, lean_object* v_b_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3663_, v_as_3664_, v_i_3665_, v_stop_3666_, v_b_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3669_, lean_object* v_env_3670_, lean_object* v_as_3671_, lean_object* v_i_3672_, lean_object* v_stop_3673_, lean_object* v_b_3674_){
_start:
{
size_t v_i_boxed_3675_; size_t v_stop_boxed_3676_; lean_object* v_res_3677_; 
v_i_boxed_3675_ = lean_unbox_usize(v_i_3672_);
lean_dec(v_i_3672_);
v_stop_boxed_3676_ = lean_unbox_usize(v_stop_3673_);
lean_dec(v_stop_3673_);
v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3669_, v_env_3670_, v_as_3671_, v_i_boxed_3675_, v_stop_boxed_3676_, v_b_3674_);
lean_dec_ref(v_as_3671_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3678_, lean_object* v_newState_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3679_, v_x_3680_, v_x_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3683_, lean_object* v_newState_3684_, lean_object* v_x_3685_, lean_object* v_x_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3683_, v_newState_3684_, v_x_3685_, v_x_3686_);
lean_dec(v_newState_3684_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3688_, lean_object* v_validate_3689_, lean_object* v_a_3690_, lean_object* v_ref_3691_, uint8_t v_applicationTime_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3689_, v_a_3690_, v_ref_3691_, v_applicationTime_3692_, v_a_3693_, v_a_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3696_, lean_object* v_validate_3697_, lean_object* v_a_3698_, lean_object* v_ref_3699_, lean_object* v_applicationTime_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
uint8_t v_applicationTime_boxed_3703_; lean_object* v_res_3704_; 
v_applicationTime_boxed_3703_ = lean_unbox(v_applicationTime_3700_);
v_res_3704_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3696_, v_validate_3697_, v_a_3698_, v_ref_3699_, v_applicationTime_boxed_3703_, v_a_3701_, v_a_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3705_, lean_object* v_attr_3706_, lean_object* v_env_3707_, lean_object* v_decl_3708_){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = lean_box(1);
v___x_3710_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3707_, v_decl_3708_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_ext_3711_; lean_object* v_toEnvExtension_3712_; lean_object* v_asyncMode_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_dec(v_inst_3705_);
v_ext_3711_ = lean_ctor_get(v_attr_3706_, 1);
lean_inc_ref(v_ext_3711_);
lean_dec_ref(v_attr_3706_);
v_toEnvExtension_3712_ = lean_ctor_get(v_ext_3711_, 0);
v_asyncMode_3713_ = lean_ctor_get(v_toEnvExtension_3712_, 2);
lean_inc(v_asyncMode_3713_);
lean_inc(v_decl_3708_);
v___x_3714_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3709_, v_ext_3711_, v_env_3707_, v_asyncMode_3713_, v_decl_3708_);
lean_dec(v_asyncMode_3713_);
lean_dec_ref(v_ext_3711_);
v___x_3715_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3714_, v_decl_3708_);
lean_dec(v_decl_3708_);
lean_dec(v___x_3714_);
return v___x_3715_;
}
else
{
lean_object* v_val_3716_; lean_object* v_ext_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3747_; 
v_val_3716_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_val_3716_);
lean_dec_ref_known(v___x_3710_, 1);
v_ext_3717_ = lean_ctor_get(v_attr_3706_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_attr_3706_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; 
v_unused_3748_ = lean_ctor_get(v_attr_3706_, 0);
lean_dec(v_unused_3748_);
v___x_3719_ = v_attr_3706_;
v_isShared_3720_ = v_isSharedCheck_3747_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_ext_3717_);
lean_dec(v_attr_3706_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3747_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
uint8_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3721_ = 0;
v___x_3722_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3709_, v_ext_3717_, v_env_3707_, v_val_3716_, v___x_3721_);
lean_dec(v_val_3716_);
lean_dec_ref(v_env_3707_);
lean_dec_ref(v_ext_3717_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = lean_array_get_size(v___x_3722_);
v___x_3725_ = lean_nat_dec_lt(v___x_3723_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; 
lean_dec_ref(v___x_3722_);
lean_del_object(v___x_3719_);
lean_dec(v_decl_3708_);
lean_dec(v_inst_3705_);
v___x_3726_ = lean_box(0);
return v___x_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3727_ = lean_unsigned_to_nat(1u);
v___x_3728_ = lean_nat_sub(v___x_3724_, v___x_3727_);
v___x_3729_ = lean_nat_dec_le(v___x_3723_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; 
lean_dec(v___x_3728_);
lean_dec_ref(v___x_3722_);
lean_del_object(v___x_3719_);
lean_dec(v_decl_3708_);
lean_dec(v_inst_3705_);
v___x_3730_ = lean_box(0);
return v___x_3730_;
}
else
{
lean_object* v___f_3731_; lean_object* v___x_3733_; 
v___f_3731_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 1, v_inst_3705_);
lean_ctor_set(v___x_3719_, 0, v_decl_3708_);
v___x_3733_ = v___x_3719_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_decl_3708_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_inst_3705_);
v___x_3733_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3735_ = l_Array_binSearchAux___redArg(v___f_3731_, v___x_3734_, v___x_3722_, v___x_3733_, v___x_3723_, v___x_3728_);
lean_dec_ref(v___x_3722_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_box(0);
return v___x_3736_;
}
else
{
lean_object* v_val_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3745_; 
v_val_3737_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3739_ = v___x_3735_;
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_val_3737_);
lean_dec(v___x_3735_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_snd_3741_; lean_object* v___x_3743_; 
v_snd_3741_ = lean_ctor_get(v_val_3737_, 1);
lean_inc(v_snd_3741_);
lean_dec(v_val_3737_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_snd_3741_);
v___x_3743_ = v___x_3739_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_snd_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3749_, lean_object* v_inst_3750_, lean_object* v_attr_3751_, lean_object* v_env_3752_, lean_object* v_decl_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3750_, v_attr_3751_, v_env_3752_, v_decl_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3763_, lean_object* v_env_3764_, lean_object* v_decl_3765_, lean_object* v_val_3766_){
_start:
{
lean_object* v_ext_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3830_; 
v_ext_3767_ = lean_ctor_get(v_attrs_3763_, 1);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_attrs_3763_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v_attrs_3763_, 0);
lean_dec(v_unused_3831_);
v___x_3769_ = v_attrs_3763_;
v_isShared_3770_ = v_isSharedCheck_3830_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_ext_3767_);
lean_dec(v_attrs_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3830_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_toEnvExtension_3771_; lean_object* v_name_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v_pfx_3782_; lean_object* v___x_3783_; 
v_toEnvExtension_3771_ = lean_ctor_get(v_ext_3767_, 0);
v_name_3772_ = lean_ctor_get(v_ext_3767_, 1);
v___x_3773_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3774_ = 1;
lean_inc(v_name_3772_);
v___x_3775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3772_, v___x_3774_);
v___x_3776_ = lean_string_append(v___x_3773_, v___x_3775_);
lean_dec_ref(v___x_3775_);
v___x_3777_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3778_ = lean_string_append(v___x_3776_, v___x_3777_);
lean_inc(v_decl_3765_);
v___x_3779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3765_, v___x_3774_);
v___x_3780_ = lean_string_append(v___x_3778_, v___x_3779_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
v___x_3783_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3764_, v_decl_3765_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_asyncMode_3784_; uint8_t v___x_3785_; 
v_asyncMode_3784_ = lean_ctor_get(v_toEnvExtension_3771_, 2);
lean_inc(v_asyncMode_3784_);
lean_inc(v_decl_3765_);
lean_inc_ref(v_env_3764_);
v___x_3785_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3764_, v_decl_3765_, v_asyncMode_3784_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___y_3789_; lean_object* v___x_3793_; 
lean_dec(v_asyncMode_3784_);
lean_del_object(v___x_3769_);
lean_dec_ref(v_ext_3767_);
lean_dec(v_val_3766_);
lean_dec(v_decl_3765_);
v___x_3786_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3787_ = lean_string_append(v_pfx_3782_, v___x_3786_);
v___x_3793_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3764_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v___x_3794_; 
v___x_3794_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3789_ = v___x_3794_;
goto v___jp_3788_;
}
else
{
lean_object* v_val_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_val_3795_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_val_3795_);
lean_dec_ref_known(v___x_3793_, 1);
v___x_3796_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3795_, v___x_3774_);
v___x_3798_ = l_addParenHeuristic(v___x_3797_);
v___x_3799_ = lean_string_append(v___x_3796_, v___x_3798_);
lean_dec_ref(v___x_3798_);
v___x_3800_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3801_ = lean_string_append(v___x_3799_, v___x_3800_);
v___y_3789_ = v___x_3801_;
goto v___jp_3788_;
}
v___jp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_string_append(v___x_3787_, v___y_3789_);
lean_dec_ref(v___y_3789_);
v___x_3791_ = lean_string_append(v___x_3790_, v___x_3781_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = lean_box(1);
lean_inc(v_decl_3765_);
lean_inc_ref(v_env_3764_);
v___x_3803_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3802_, v_ext_3767_, v_env_3764_, v_asyncMode_3784_, v_decl_3765_);
v___x_3804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3803_, v_decl_3765_);
lean_dec(v___x_3803_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v___x_3806_; 
lean_dec_ref(v_pfx_3782_);
lean_inc(v_decl_3765_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 1, v_val_3766_);
lean_ctor_set(v___x_3769_, 0, v_decl_3765_);
v___x_3806_ = v___x_3769_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_decl_3765_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_val_3766_);
v___x_3806_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3767_, v_env_3764_, v___x_3806_, v_asyncMode_3784_, v_decl_3765_);
lean_dec(v_asyncMode_3784_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
return v___x_3808_;
}
}
else
{
lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3818_; 
lean_dec(v_asyncMode_3784_);
lean_del_object(v___x_3769_);
lean_dec_ref(v_ext_3767_);
lean_dec(v_val_3766_);
lean_dec(v_decl_3765_);
lean_dec_ref(v_env_3764_);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v___x_3804_, 0);
lean_dec(v_unused_3819_);
v___x_3811_ = v___x_3804_;
v_isShared_3812_ = v_isSharedCheck_3818_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v___x_3804_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3818_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3813_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3814_ = lean_string_append(v_pfx_3782_, v___x_3813_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set_tag(v___x_3811_, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3814_);
v___x_3816_ = v___x_3811_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
else
{
lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3828_; 
lean_del_object(v___x_3769_);
lean_dec_ref(v_ext_3767_);
lean_dec(v_val_3766_);
lean_dec(v_decl_3765_);
lean_dec_ref(v_env_3764_);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3828_ == 0)
{
lean_object* v_unused_3829_; 
v_unused_3829_ = lean_ctor_get(v___x_3783_, 0);
lean_dec(v_unused_3829_);
v___x_3821_ = v___x_3783_;
v_isShared_3822_ = v_isSharedCheck_3828_;
goto v_resetjp_3820_;
}
else
{
lean_dec(v___x_3783_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3828_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3823_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3824_ = lean_string_append(v_pfx_3782_, v___x_3823_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3824_);
v___x_3826_ = v___x_3821_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3832_, lean_object* v_attrs_3833_, lean_object* v_env_3834_, lean_object* v_decl_3835_, lean_object* v_val_3836_){
_start:
{
lean_object* v___x_3837_; 
v___x_3837_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3833_, v_env_3834_, v_decl_3835_, v_val_3836_);
return v___x_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3840_ = lean_st_mk_ref(v___x_3839_);
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3846_, lean_object* v_builder_3847_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3849_ = l_Lean_attributeImplBuilderTableRef;
v___x_3850_ = lean_st_ref_get(v___x_3849_);
v___x_3851_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3850_, v_builderId_3846_);
lean_dec(v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3852_ = lean_st_ref_take(v___x_3849_);
v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3852_, v_builderId_3846_, v_builder_3847_);
v___x_3854_ = lean_st_ref_put(v___x_3849_, v___x_3853_);
v___x_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
return v___x_3855_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec_ref(v_builder_3847_);
v___x_3856_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3857_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3846_, v___x_3851_);
v___x_3858_ = lean_string_append(v___x_3856_, v___x_3857_);
lean_dec_ref(v___x_3857_);
v___x_3859_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3860_ = lean_string_append(v___x_3858_, v___x_3859_);
v___x_3861_ = lean_mk_io_user_error(v___x_3860_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3863_, lean_object* v_builder_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_registerAttributeImplBuilder(v_builderId_3863_, v_builder_3864_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3867_){
_start:
{
if (lean_obj_tag(v_e_3867_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3877_; 
v_a_3869_ = lean_ctor_get(v_e_3867_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_e_3867_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3871_ = v_e_3867_;
v_isShared_3872_ = v_isSharedCheck_3877_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v_e_3867_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3877_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3873_ = lean_mk_io_user_error(v_a_3869_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set_tag(v___x_3871_, 1);
lean_ctor_set(v___x_3871_, 0, v___x_3873_);
v___x_3875_ = v___x_3871_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
v_a_3878_ = lean_ctor_get(v_e_3867_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_e_3867_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v_e_3867_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v_e_3867_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set_tag(v___x_3880_, 0);
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3889_, lean_object* v_e_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3893_, lean_object* v_e_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3893_, v_e_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3897_, lean_object* v_x_3898_){
_start:
{
if (lean_obj_tag(v_x_3898_) == 0)
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_box(0);
return v___x_3899_;
}
else
{
lean_object* v_key_3900_; lean_object* v_value_3901_; lean_object* v_tail_3902_; uint8_t v___x_3903_; 
v_key_3900_ = lean_ctor_get(v_x_3898_, 0);
v_value_3901_ = lean_ctor_get(v_x_3898_, 1);
v_tail_3902_ = lean_ctor_get(v_x_3898_, 2);
v___x_3903_ = lean_name_eq(v_key_3900_, v_a_3897_);
if (v___x_3903_ == 0)
{
v_x_3898_ = v_tail_3902_;
goto _start;
}
else
{
lean_object* v___x_3905_; 
lean_inc(v_value_3901_);
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v_value_3901_);
return v___x_3905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3906_, lean_object* v_x_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3906_, v_x_3907_);
lean_dec(v_x_3907_);
lean_dec(v_a_3906_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_buckets_3911_; lean_object* v___x_3912_; uint64_t v___y_3914_; 
v_buckets_3911_ = lean_ctor_get(v_m_3909_, 1);
v___x_3912_ = lean_array_get_size(v_buckets_3911_);
if (lean_obj_tag(v_a_3910_) == 0)
{
uint64_t v___x_3928_; 
v___x_3928_ = 1723ULL;
v___y_3914_ = v___x_3928_;
goto v___jp_3913_;
}
else
{
uint64_t v_hash_3929_; 
v_hash_3929_ = lean_ctor_get_uint64(v_a_3910_, sizeof(void*)*2);
v___y_3914_ = v_hash_3929_;
goto v___jp_3913_;
}
v___jp_3913_:
{
uint64_t v___x_3915_; uint64_t v___x_3916_; uint64_t v_fold_3917_; uint64_t v___x_3918_; uint64_t v___x_3919_; uint64_t v___x_3920_; size_t v___x_3921_; size_t v___x_3922_; size_t v___x_3923_; size_t v___x_3924_; size_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3915_ = 32ULL;
v___x_3916_ = lean_uint64_shift_right(v___y_3914_, v___x_3915_);
v_fold_3917_ = lean_uint64_xor(v___y_3914_, v___x_3916_);
v___x_3918_ = 16ULL;
v___x_3919_ = lean_uint64_shift_right(v_fold_3917_, v___x_3918_);
v___x_3920_ = lean_uint64_xor(v_fold_3917_, v___x_3919_);
v___x_3921_ = lean_uint64_to_usize(v___x_3920_);
v___x_3922_ = lean_usize_of_nat(v___x_3912_);
v___x_3923_ = ((size_t)1ULL);
v___x_3924_ = lean_usize_sub(v___x_3922_, v___x_3923_);
v___x_3925_ = lean_usize_land(v___x_3921_, v___x_3924_);
v___x_3926_ = lean_array_uget_borrowed(v_buckets_3911_, v___x_3925_);
v___x_3927_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3910_, v___x_3926_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3930_, v_a_3931_);
lean_dec(v_a_3931_);
lean_dec_ref(v_m_3930_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3934_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v_builderId_3938_; lean_object* v_ref_3939_; lean_object* v_args_3940_; lean_object* v___x_3941_; 
v___x_3936_ = l_Lean_attributeImplBuilderTableRef;
v___x_3937_ = lean_st_ref_get(v___x_3936_);
v_builderId_3938_ = lean_ctor_get(v_e_3934_, 0);
lean_inc(v_builderId_3938_);
v_ref_3939_ = lean_ctor_get(v_e_3934_, 1);
lean_inc(v_ref_3939_);
v_args_3940_ = lean_ctor_get(v_e_3934_, 2);
lean_inc(v_args_3940_);
lean_dec_ref(v_e_3934_);
v___x_3941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3937_, v_builderId_3938_);
lean_dec(v___x_3937_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_args_3940_);
lean_dec(v_ref_3939_);
v___x_3942_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3943_ = 1;
v___x_3944_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3938_, v___x_3943_);
v___x_3945_ = lean_string_append(v___x_3942_, v___x_3944_);
lean_dec_ref(v___x_3944_);
v___x_3946_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3947_ = lean_string_append(v___x_3945_, v___x_3946_);
v___x_3948_ = lean_mk_io_user_error(v___x_3947_);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
return v___x_3949_;
}
else
{
lean_object* v_val_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_dec(v_builderId_3938_);
v_val_3950_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_val_3950_);
lean_dec_ref_known(v___x_3941_, 1);
v___x_3951_ = lean_apply_2(v_val_3950_, v_ref_3939_, v_args_3940_);
v___x_3952_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3951_);
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_mkAttributeImplOfEntry(v_e_3953_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3956_, lean_object* v_m_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3957_, v_a_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3960_, lean_object* v_m_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3960_, v_m_3961_, v_a_3962_);
lean_dec(v_a_3962_);
lean_dec_ref(v_m_3961_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3964_, lean_object* v_a_3965_, lean_object* v_x_3966_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3965_, v_x_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3968_, lean_object* v_a_3969_, lean_object* v_x_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3968_, v_a_3969_, v_x_3970_);
lean_dec(v_x_3970_);
lean_dec(v_a_3969_);
return v_res_3971_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3972_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3973_ = lean_box(0);
v___x_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
lean_ctor_set(v___x_3974_, 1, v___x_3972_);
return v___x_3974_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3975_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3978_ = l_Lean_attributeMapRef;
v___x_3979_ = lean_st_ref_get(v___x_3978_);
v___x_3980_ = lean_box(0);
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
lean_ctor_set(v___x_3981_, 1, v___x_3979_);
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3990_, lean_object* v_opts_3991_, lean_object* v_declName_3992_){
_start:
{
uint8_t v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = 0;
lean_inc(v_declName_3992_);
lean_inc_ref(v_env_3990_);
v___x_3996_ = l_Lean_Environment_find_x3f(v_env_3990_, v_declName_3992_, v___x_3995_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec_ref(v_env_3990_);
v___x_3997_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3998_ = 1;
v___x_3999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3992_, v___x_3998_);
v___x_4000_ = lean_string_append(v___x_3997_, v___x_3999_);
lean_dec_ref(v___x_3999_);
v___x_4001_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4002_ = lean_string_append(v___x_4000_, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
return v___x_4003_;
}
else
{
lean_object* v_val_4004_; lean_object* v___x_4005_; 
v_val_4004_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_val_4004_);
lean_dec_ref_known(v___x_3996_, 1);
v___x_4005_ = l_Lean_ConstantInfo_type(v_val_4004_);
lean_dec(v_val_4004_);
if (lean_obj_tag(v___x_4005_) == 4)
{
lean_object* v_declName_4006_; 
v_declName_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_declName_4006_);
lean_dec_ref_known(v___x_4005_, 2);
if (lean_obj_tag(v_declName_4006_) == 1)
{
lean_object* v_pre_4007_; 
v_pre_4007_ = lean_ctor_get(v_declName_4006_, 0);
lean_inc(v_pre_4007_);
if (lean_obj_tag(v_pre_4007_) == 1)
{
lean_object* v_pre_4008_; 
v_pre_4008_ = lean_ctor_get(v_pre_4007_, 0);
if (lean_obj_tag(v_pre_4008_) == 0)
{
lean_object* v_str_4009_; lean_object* v_str_4010_; lean_object* v___x_4011_; uint8_t v___x_4012_; 
v_str_4009_ = lean_ctor_get(v_declName_4006_, 1);
lean_inc_ref(v_str_4009_);
lean_dec_ref_known(v_declName_4006_, 2);
v_str_4010_ = lean_ctor_get(v_pre_4007_, 1);
lean_inc_ref(v_str_4010_);
lean_dec_ref_known(v_pre_4007_, 2);
v___x_4011_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4012_ = lean_string_dec_eq(v_str_4010_, v___x_4011_);
lean_dec_ref(v_str_4010_);
if (v___x_4012_ == 0)
{
lean_dec_ref(v_str_4009_);
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
goto v___jp_3993_;
}
else
{
lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4013_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4014_ = lean_string_dec_eq(v_str_4009_, v___x_4013_);
lean_dec_ref(v_str_4009_);
if (v___x_4014_ == 0)
{
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
goto v___jp_3993_;
}
else
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_Environment_evalConst___redArg(v_env_3990_, v_opts_3991_, v_declName_3992_, v___x_4014_);
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
return v___x_4015_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4007_, 2);
lean_dec_ref_known(v_declName_4006_, 2);
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
goto v___jp_3993_;
}
}
else
{
lean_dec(v_pre_4007_);
lean_dec_ref_known(v_declName_4006_, 2);
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
goto v___jp_3993_;
}
}
else
{
lean_dec(v_declName_4006_);
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
goto v___jp_3993_;
}
}
else
{
lean_dec_ref(v___x_4005_);
lean_dec(v_declName_3992_);
lean_dec_ref(v_env_3990_);
goto v___jp_3993_;
}
}
v___jp_3993_:
{
lean_object* v___x_3994_; 
v___x_3994_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4016_, lean_object* v_opts_4017_, lean_object* v_declName_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4016_, v_opts_4017_, v_declName_4018_);
lean_dec_ref(v_opts_4017_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4020_, size_t v_i_4021_, size_t v_stop_4022_, lean_object* v_b_4023_){
_start:
{
uint8_t v___x_4025_; 
v___x_4025_ = lean_usize_dec_eq(v_i_4021_, v_stop_4022_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_array_uget_borrowed(v_as_4020_, v_i_4021_);
lean_inc(v___x_4026_);
v___x_4027_ = l_Lean_mkAttributeImplOfEntry(v___x_4026_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v_toAttributeImplCore_4029_; lean_object* v_name_4030_; lean_object* v___x_4031_; size_t v___x_4032_; size_t v___x_4033_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v_toAttributeImplCore_4029_ = lean_ctor_get(v_a_4028_, 0);
v_name_4030_ = lean_ctor_get(v_toAttributeImplCore_4029_, 1);
lean_inc(v_name_4030_);
v___x_4031_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4023_, v_name_4030_, v_a_4028_);
v___x_4032_ = ((size_t)1ULL);
v___x_4033_ = lean_usize_add(v_i_4021_, v___x_4032_);
v_i_4021_ = v___x_4033_;
v_b_4023_ = v___x_4031_;
goto _start;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v_b_4023_);
v_a_4035_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4027_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4027_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_object* v___x_4043_; 
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v_b_4023_);
return v___x_4043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4044_, lean_object* v_i_4045_, lean_object* v_stop_4046_, lean_object* v_b_4047_, lean_object* v___y_4048_){
_start:
{
size_t v_i_boxed_4049_; size_t v_stop_boxed_4050_; lean_object* v_res_4051_; 
v_i_boxed_4049_ = lean_unbox_usize(v_i_4045_);
lean_dec(v_i_4045_);
v_stop_boxed_4050_ = lean_unbox_usize(v_stop_4046_);
lean_dec(v_stop_4046_);
v_res_4051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4044_, v_i_boxed_4049_, v_stop_boxed_4050_, v_b_4047_);
lean_dec_ref(v_as_4044_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4052_, size_t v_i_4053_, size_t v_stop_4054_, lean_object* v_b_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_a_4059_; lean_object* v___y_4064_; uint8_t v___x_4066_; 
v___x_4066_ = lean_usize_dec_eq(v_i_4053_, v_stop_4054_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v___x_4067_ = lean_array_uget_borrowed(v_as_4052_, v_i_4053_);
v___x_4068_ = lean_unsigned_to_nat(0u);
v___x_4069_ = lean_array_get_size(v___x_4067_);
v___x_4070_ = lean_nat_dec_lt(v___x_4068_, v___x_4069_);
if (v___x_4070_ == 0)
{
v_a_4059_ = v_b_4055_;
goto v___jp_4058_;
}
else
{
uint8_t v___x_4071_; 
v___x_4071_ = lean_nat_dec_le(v___x_4069_, v___x_4069_);
if (v___x_4071_ == 0)
{
if (v___x_4070_ == 0)
{
v_a_4059_ = v_b_4055_;
goto v___jp_4058_;
}
else
{
size_t v___x_4072_; size_t v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = ((size_t)0ULL);
v___x_4073_ = lean_usize_of_nat(v___x_4069_);
v___x_4074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4067_, v___x_4072_, v___x_4073_, v_b_4055_);
v___y_4064_ = v___x_4074_;
goto v___jp_4063_;
}
}
else
{
size_t v___x_4075_; size_t v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = ((size_t)0ULL);
v___x_4076_ = lean_usize_of_nat(v___x_4069_);
v___x_4077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4067_, v___x_4075_, v___x_4076_, v_b_4055_);
v___y_4064_ = v___x_4077_;
goto v___jp_4063_;
}
}
}
else
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_b_4055_);
return v___x_4078_;
}
v___jp_4058_:
{
size_t v___x_4060_; size_t v___x_4061_; 
v___x_4060_ = ((size_t)1ULL);
v___x_4061_ = lean_usize_add(v_i_4053_, v___x_4060_);
v_i_4053_ = v___x_4061_;
v_b_4055_ = v_a_4059_;
goto _start;
}
v___jp_4063_:
{
if (lean_obj_tag(v___y_4064_) == 0)
{
lean_object* v_a_4065_; 
v_a_4065_ = lean_ctor_get(v___y_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___y_4064_, 1);
v_a_4059_ = v_a_4065_;
goto v___jp_4058_;
}
else
{
return v___y_4064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4079_, lean_object* v_i_4080_, lean_object* v_stop_4081_, lean_object* v_b_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
size_t v_i_boxed_4085_; size_t v_stop_boxed_4086_; lean_object* v_res_4087_; 
v_i_boxed_4085_ = lean_unbox_usize(v_i_4080_);
lean_dec(v_i_4080_);
v_stop_boxed_4086_ = lean_unbox_usize(v_stop_4081_);
lean_dec(v_stop_4081_);
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4079_, v_i_boxed_4085_, v_stop_boxed_4086_, v_b_4082_, v___y_4083_);
lean_dec_ref(v___y_4083_);
lean_dec_ref(v_as_4079_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_a_4092_; lean_object* v___y_4097_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4107_ = l_Lean_attributeMapRef;
v___x_4108_ = lean_st_ref_get(v___x_4107_);
v___x_4109_ = lean_unsigned_to_nat(0u);
v___x_4110_ = lean_array_get_size(v_es_4088_);
v___x_4111_ = lean_nat_dec_lt(v___x_4109_, v___x_4110_);
if (v___x_4111_ == 0)
{
v_a_4092_ = v___x_4108_;
goto v___jp_4091_;
}
else
{
uint8_t v___x_4112_; 
v___x_4112_ = lean_nat_dec_le(v___x_4110_, v___x_4110_);
if (v___x_4112_ == 0)
{
if (v___x_4111_ == 0)
{
v_a_4092_ = v___x_4108_;
goto v___jp_4091_;
}
else
{
size_t v___x_4113_; size_t v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = ((size_t)0ULL);
v___x_4114_ = lean_usize_of_nat(v___x_4110_);
v___x_4115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4088_, v___x_4113_, v___x_4114_, v___x_4108_, v_a_4089_);
v___y_4097_ = v___x_4115_;
goto v___jp_4096_;
}
}
else
{
size_t v___x_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
v___x_4116_ = ((size_t)0ULL);
v___x_4117_ = lean_usize_of_nat(v___x_4110_);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4088_, v___x_4116_, v___x_4117_, v___x_4108_, v_a_4089_);
v___y_4097_ = v___x_4118_;
goto v___jp_4096_;
}
}
v___jp_4091_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4093_ = lean_box(0);
v___x_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
lean_ctor_set(v___x_4094_, 1, v_a_4092_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
v___jp_4096_:
{
if (lean_obj_tag(v___y_4097_) == 0)
{
lean_object* v_a_4098_; 
v_a_4098_ = lean_ctor_get(v___y_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___y_4097_, 1);
v_a_4092_ = v_a_4098_;
goto v___jp_4091_;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
v_a_4099_ = lean_ctor_get(v___y_4097_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___y_4097_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___y_4097_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___y_4097_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4119_, v_a_4120_);
lean_dec_ref(v_a_4120_);
lean_dec_ref(v_es_4119_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4123_, size_t v_i_4124_, size_t v_stop_4125_, lean_object* v_b_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4123_, v_i_4124_, v_stop_4125_, v_b_4126_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4130_, lean_object* v_i_4131_, lean_object* v_stop_4132_, lean_object* v_b_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
size_t v_i_boxed_4136_; size_t v_stop_boxed_4137_; lean_object* v_res_4138_; 
v_i_boxed_4136_ = lean_unbox_usize(v_i_4131_);
lean_dec(v_i_4131_);
v_stop_boxed_4137_ = lean_unbox_usize(v_stop_4132_);
lean_dec(v_stop_4132_);
v_res_4138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4130_, v_i_boxed_4136_, v_stop_boxed_4137_, v_b_4133_, v___y_4134_);
lean_dec_ref(v___y_4134_);
lean_dec_ref(v_as_4130_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4139_, lean_object* v_e_4140_){
_start:
{
lean_object* v_snd_4141_; lean_object* v_toAttributeImplCore_4142_; lean_object* v_fst_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4161_; 
v_snd_4141_ = lean_ctor_get(v_e_4140_, 1);
lean_inc(v_snd_4141_);
v_toAttributeImplCore_4142_ = lean_ctor_get(v_snd_4141_, 0);
v_fst_4143_ = lean_ctor_get(v_e_4140_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_e_4140_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v_e_4140_, 1);
lean_dec(v_unused_4162_);
v___x_4145_ = v_e_4140_;
v_isShared_4146_ = v_isSharedCheck_4161_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_fst_4143_);
lean_dec(v_e_4140_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4161_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v_newEntries_4147_; lean_object* v_map_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4160_; 
v_newEntries_4147_ = lean_ctor_get(v_s_4139_, 0);
v_map_4148_ = lean_ctor_get(v_s_4139_, 1);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_s_4139_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4150_ = v_s_4139_;
v_isShared_4151_ = v_isSharedCheck_4160_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_map_4148_);
lean_inc(v_newEntries_4147_);
lean_dec(v_s_4139_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4160_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v_name_4152_; lean_object* v___x_4154_; 
v_name_4152_ = lean_ctor_get(v_toAttributeImplCore_4142_, 1);
lean_inc(v_name_4152_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set_tag(v___x_4145_, 1);
lean_ctor_set(v___x_4145_, 1, v_newEntries_4147_);
v___x_4154_ = v___x_4145_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_fst_4143_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_newEntries_4147_);
v___x_4154_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4148_, v_name_4152_, v_snd_4141_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v___x_4155_);
lean_ctor_set(v___x_4150_, 0, v___x_4154_);
v___x_4157_ = v___x_4150_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v___x_4155_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4163_, lean_object* v_s_4164_){
_start:
{
lean_object* v_newEntries_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_newEntries_4165_ = lean_ctor_get(v_s_4164_, 0);
lean_inc(v_newEntries_4165_);
lean_dec_ref(v_s_4164_);
v___x_4166_ = l_List_reverse___redArg(v_newEntries_4165_);
v___x_4167_ = lean_array_mk(v___x_4166_);
lean_inc_ref_n(v___x_4167_, 2);
v___x_4168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
lean_ctor_set(v___x_4168_, 2, v___x_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4169_, lean_object* v_s_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4169_, v_s_4170_);
lean_dec_ref(v_x_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4172_){
_start:
{
lean_object* v_newEntries_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4184_; 
v_newEntries_4173_ = lean_ctor_get(v_s_4172_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_s_4172_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; 
v_unused_4185_ = lean_ctor_get(v_s_4172_, 1);
lean_dec(v_unused_4185_);
v___x_4175_ = v_s_4172_;
v_isShared_4176_ = v_isSharedCheck_4184_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_newEntries_4173_);
lean_dec(v_s_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4184_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4182_; 
v___x_4177_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4178_ = l_List_lengthTR___redArg(v_newEntries_4173_);
lean_dec(v_newEntries_4173_);
v___x_4179_ = l_Nat_reprFast(v___x_4178_);
v___x_4180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set_tag(v___x_4175_, 5);
lean_ctor_set(v___x_4175_, 1, v___x_4180_);
lean_ctor_set(v___x_4175_, 0, v___x_4177_);
v___x_4182_ = v___x_4175_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4186_){
_start:
{
lean_object* v_newEntries_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_newEntries_4187_ = lean_ctor_get(v_s_4186_, 0);
lean_inc(v_newEntries_4187_);
lean_dec_ref(v_s_4186_);
v___x_4188_ = l_List_reverse___redArg(v_newEntries_4187_);
v___x_4189_ = lean_array_mk(v___x_4188_);
return v___x_4189_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___f_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4199_ = lean_box(0);
v___x_4200_ = lean_box(2);
v___f_4201_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4202_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4203_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4204_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4205_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4206_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4207_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
lean_ctor_set(v___x_4207_, 1, v___x_4205_);
lean_ctor_set(v___x_4207_, 2, v___x_4204_);
lean_ctor_set(v___x_4207_, 3, v___x_4203_);
lean_ctor_set(v___x_4207_, 4, v___f_4202_);
lean_ctor_set(v___x_4207_, 5, v___f_4201_);
lean_ctor_set(v___x_4207_, 6, v___x_4200_);
lean_ctor_set(v___x_4207_, 7, v___x_4199_);
return v___x_4207_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___f_4208_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4209_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
lean_ctor_set(v___x_4210_, 1, v___f_4208_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4213_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4216_){
_start:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4218_ = l_Lean_attributeMapRef;
v___x_4219_ = lean_st_ref_get(v___x_4218_);
v___x_4220_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4219_, v_n_4216_);
lean_dec(v___x_4219_);
v___x_4221_ = lean_box(v___x_4220_);
v___x_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_isBuiltinAttribute(v_n_4223_);
lean_dec(v_n_4223_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4226_, lean_object* v_x_4227_){
_start:
{
if (lean_obj_tag(v_x_4227_) == 0)
{
return v_x_4226_;
}
else
{
lean_object* v_key_4228_; lean_object* v_tail_4229_; lean_object* v___x_4230_; 
v_key_4228_ = lean_ctor_get(v_x_4227_, 0);
v_tail_4229_ = lean_ctor_get(v_x_4227_, 2);
lean_inc(v_key_4228_);
v___x_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4230_, 0, v_key_4228_);
lean_ctor_set(v___x_4230_, 1, v_x_4226_);
v_x_4226_ = v___x_4230_;
v_x_4227_ = v_tail_4229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4232_, lean_object* v_x_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4232_, v_x_4233_);
lean_dec(v_x_4233_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4235_, size_t v_i_4236_, size_t v_stop_4237_, lean_object* v_b_4238_){
_start:
{
uint8_t v___x_4239_; 
v___x_4239_ = lean_usize_dec_eq(v_i_4236_, v_stop_4237_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; size_t v___x_4242_; size_t v___x_4243_; 
v___x_4240_ = lean_array_uget_borrowed(v_as_4235_, v_i_4236_);
v___x_4241_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4238_, v___x_4240_);
v___x_4242_ = ((size_t)1ULL);
v___x_4243_ = lean_usize_add(v_i_4236_, v___x_4242_);
v_i_4236_ = v___x_4243_;
v_b_4238_ = v___x_4241_;
goto _start;
}
else
{
return v_b_4238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4245_, lean_object* v_i_4246_, lean_object* v_stop_4247_, lean_object* v_b_4248_){
_start:
{
size_t v_i_boxed_4249_; size_t v_stop_boxed_4250_; lean_object* v_res_4251_; 
v_i_boxed_4249_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_stop_boxed_4250_ = lean_unbox_usize(v_stop_4247_);
lean_dec(v_stop_4247_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4245_, v_i_boxed_4249_, v_stop_boxed_4250_, v_b_4248_);
lean_dec_ref(v_as_4245_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v_buckets_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v___x_4253_ = l_Lean_attributeMapRef;
v___x_4254_ = lean_st_ref_get(v___x_4253_);
v_buckets_4255_ = lean_ctor_get(v___x_4254_, 1);
lean_inc_ref(v_buckets_4255_);
lean_dec(v___x_4254_);
v___x_4256_ = lean_box(0);
v___x_4257_ = lean_unsigned_to_nat(0u);
v___x_4258_ = lean_array_get_size(v_buckets_4255_);
v___x_4259_ = lean_nat_dec_lt(v___x_4257_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; 
lean_dec_ref(v_buckets_4255_);
v___x_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4256_);
return v___x_4260_;
}
else
{
size_t v___x_4261_; size_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4261_ = ((size_t)0ULL);
v___x_4262_ = lean_usize_of_nat(v___x_4258_);
v___x_4263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4255_, v___x_4261_, v___x_4262_, v___x_4256_);
lean_dec_ref(v_buckets_4255_);
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
return v___x_4264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_getBuiltinAttributeNames();
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4268_){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = l_Lean_attributeMapRef;
v___x_4271_ = lean_st_ref_get(v___x_4270_);
v___x_4272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4271_, v_attrName_4268_);
lean_dec(v___x_4271_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v___x_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4273_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4274_ = 1;
v___x_4275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4268_, v___x_4274_);
v___x_4276_ = lean_string_append(v___x_4273_, v___x_4275_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4278_ = lean_string_append(v___x_4276_, v___x_4277_);
v___x_4279_ = lean_mk_io_user_error(v___x_4278_);
v___x_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
else
{
lean_object* v_val_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_attrName_4268_);
v_val_4281_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4272_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_val_4281_);
lean_dec(v___x_4272_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 0);
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_val_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4289_, lean_object* v_a_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4289_);
return v_res_4291_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4292_, lean_object* v_attrName_4293_){
_start:
{
lean_object* v___x_4294_; lean_object* v_toEnvExtension_4295_; lean_object* v_asyncMode_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v_map_4300_; uint8_t v___x_4301_; 
v___x_4294_ = l_Lean_attributeExtension;
v_toEnvExtension_4295_ = lean_ctor_get(v___x_4294_, 0);
v_asyncMode_4296_ = lean_ctor_get(v_toEnvExtension_4295_, 2);
v___x_4297_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4298_ = lean_box(0);
v___x_4299_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4297_, v___x_4294_, v_env_4292_, v_asyncMode_4296_, v___x_4298_);
v_map_4300_ = lean_ctor_get(v___x_4299_, 1);
lean_inc_ref(v_map_4300_);
lean_dec(v___x_4299_);
v___x_4301_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4300_, v_attrName_4293_);
lean_dec_ref(v_map_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4302_, lean_object* v_attrName_4303_){
_start:
{
uint8_t v_res_4304_; lean_object* v_r_4305_; 
v_res_4304_ = l_Lean_isAttribute(v_env_4302_, v_attrName_4303_);
lean_dec(v_attrName_4303_);
v_r_4305_ = lean_box(v_res_4304_);
return v_r_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4306_){
_start:
{
lean_object* v___x_4307_; lean_object* v_toEnvExtension_4308_; lean_object* v_asyncMode_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v_map_4313_; lean_object* v_buckets_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4307_ = l_Lean_attributeExtension;
v_toEnvExtension_4308_ = lean_ctor_get(v___x_4307_, 0);
v_asyncMode_4309_ = lean_ctor_get(v_toEnvExtension_4308_, 2);
v___x_4310_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4311_ = lean_box(0);
v___x_4312_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4310_, v___x_4307_, v_env_4306_, v_asyncMode_4309_, v___x_4311_);
v_map_4313_ = lean_ctor_get(v___x_4312_, 1);
lean_inc_ref(v_map_4313_);
lean_dec(v___x_4312_);
v_buckets_4314_ = lean_ctor_get(v_map_4313_, 1);
lean_inc_ref(v_buckets_4314_);
lean_dec_ref(v_map_4313_);
v___x_4315_ = lean_box(0);
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_array_get_size(v_buckets_4314_);
v___x_4318_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_dec_ref(v_buckets_4314_);
return v___x_4315_;
}
else
{
size_t v___x_4319_; size_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = ((size_t)0ULL);
v___x_4320_ = lean_usize_of_nat(v___x_4317_);
v___x_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4314_, v___x_4319_, v___x_4320_, v___x_4315_);
lean_dec_ref(v_buckets_4314_);
return v___x_4321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4322_, lean_object* v_attrName_4323_){
_start:
{
lean_object* v___x_4324_; lean_object* v_toEnvExtension_4325_; lean_object* v_asyncMode_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v_map_4330_; lean_object* v___x_4331_; 
v___x_4324_ = l_Lean_attributeExtension;
v_toEnvExtension_4325_ = lean_ctor_get(v___x_4324_, 0);
v_asyncMode_4326_ = lean_ctor_get(v_toEnvExtension_4325_, 2);
v___x_4327_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4328_ = lean_box(0);
v___x_4329_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4327_, v___x_4324_, v_env_4322_, v_asyncMode_4326_, v___x_4328_);
v_map_4330_ = lean_ctor_get(v___x_4329_, 1);
lean_inc_ref(v_map_4330_);
lean_dec(v___x_4329_);
v___x_4331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4330_, v_attrName_4323_);
lean_dec_ref(v_map_4330_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4332_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4333_ = 1;
v___x_4334_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4323_, v___x_4333_);
v___x_4335_ = lean_string_append(v___x_4332_, v___x_4334_);
lean_dec_ref(v___x_4334_);
v___x_4336_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4337_ = lean_string_append(v___x_4335_, v___x_4336_);
v___x_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
return v___x_4338_;
}
else
{
lean_object* v_val_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_attrName_4323_);
v_val_4339_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4331_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_val_4339_);
lean_dec(v___x_4331_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4347_, lean_object* v_builderId_4348_, lean_object* v_ref_4349_, lean_object* v_args_4350_){
_start:
{
lean_object* v_entry_4352_; lean_object* v___x_4353_; 
v_entry_4352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4352_, 0, v_builderId_4348_);
lean_ctor_set(v_entry_4352_, 1, v_ref_4349_);
lean_ctor_set(v_entry_4352_, 2, v_args_4350_);
lean_inc_ref(v_entry_4352_);
v___x_4353_ = l_Lean_mkAttributeImplOfEntry(v_entry_4352_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4379_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4356_ = v___x_4353_;
v_isShared_4357_ = v_isSharedCheck_4379_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4379_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v_toAttributeImplCore_4358_; lean_object* v_name_4359_; uint8_t v___x_4360_; 
v_toAttributeImplCore_4358_ = lean_ctor_get(v_a_4354_, 0);
v_name_4359_ = lean_ctor_get(v_toAttributeImplCore_4358_, 1);
lean_inc_ref(v_env_4347_);
v___x_4360_ = l_Lean_isAttribute(v_env_4347_, v_name_4359_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; lean_object* v_toEnvExtension_4362_; lean_object* v_asyncMode_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4361_ = l_Lean_attributeExtension;
v_toEnvExtension_4362_ = lean_ctor_get(v___x_4361_, 0);
v_asyncMode_4363_ = lean_ctor_get(v_toEnvExtension_4362_, 2);
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v_entry_4352_);
lean_ctor_set(v___x_4364_, 1, v_a_4354_);
v___x_4365_ = lean_box(0);
v___x_4366_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4361_, v_env_4347_, v___x_4364_, v_asyncMode_4363_, v___x_4365_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4366_);
v___x_4368_ = v___x_4356_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
else
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
lean_inc(v_name_4359_);
lean_dec(v_a_4354_);
lean_dec_ref_known(v_entry_4352_, 3);
lean_dec_ref(v_env_4347_);
v___x_4370_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4359_, v___x_4360_);
v___x_4372_ = lean_string_append(v___x_4370_, v___x_4371_);
lean_dec_ref(v___x_4371_);
v___x_4373_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4374_ = lean_string_append(v___x_4372_, v___x_4373_);
v___x_4375_ = lean_mk_io_user_error(v___x_4374_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set_tag(v___x_4356_, 1);
lean_ctor_set(v___x_4356_, 0, v___x_4375_);
v___x_4377_ = v___x_4356_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec_ref_known(v_entry_4352_, 3);
lean_dec_ref(v_env_4347_);
v_a_4380_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4353_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4353_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4388_, lean_object* v_builderId_4389_, lean_object* v_ref_4390_, lean_object* v_args_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_registerAttributeOfBuilder(v_env_4388_, v_builderId_4389_, v_ref_4390_, v_args_4391_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
if (lean_obj_tag(v_x_4394_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_a_4398_ = lean_ctor_get(v_x_4394_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v_x_4394_, 1);
v___x_4399_ = l_Lean_stringToMessageData(v_a_4398_);
v___x_4400_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4399_, v___y_4395_, v___y_4396_);
return v___x_4400_;
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
v_a_4401_ = lean_ctor_get(v_x_4394_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_x_4394_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v_x_4394_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v_x_4394_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set_tag(v___x_4403_, 0);
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4414_, lean_object* v_attrName_4415_, lean_object* v_stx_4416_, uint8_t v_kind_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v___x_4421_; lean_object* v_env_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4421_ = lean_st_ref_get(v_a_4419_);
v_env_4422_ = lean_ctor_get(v___x_4421_, 0);
lean_inc_ref(v_env_4422_);
lean_dec(v___x_4421_);
v___x_4423_ = l_Lean_getAttributeImpl(v_env_4422_, v_attrName_4415_);
v___x_4424_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4423_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v_add_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
v_add_4426_ = lean_ctor_get(v_a_4425_, 1);
lean_inc_ref(v_add_4426_);
lean_dec(v_a_4425_);
v___x_4427_ = lean_box(v_kind_4417_);
lean_inc(v_a_4419_);
lean_inc_ref(v_a_4418_);
v___x_4428_ = lean_apply_6(v_add_4426_, v_declName_4414_, v_stx_4416_, v___x_4427_, v_a_4418_, v_a_4419_, lean_box(0));
return v___x_4428_;
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
lean_dec(v_stx_4416_);
lean_dec(v_declName_4414_);
v_a_4429_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4424_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4424_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4437_, lean_object* v_attrName_4438_, lean_object* v_stx_4439_, lean_object* v_kind_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
uint8_t v_kind_boxed_4444_; lean_object* v_res_4445_; 
v_kind_boxed_4444_ = lean_unbox(v_kind_4440_);
v_res_4445_ = l_Lean_Attribute_add(v_declName_4437_, v_attrName_4438_, v_stx_4439_, v_kind_boxed_4444_, v_a_4441_, v_a_4442_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4446_, lean_object* v_x_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4447_, v___y_4448_, v___y_4449_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4452_, lean_object* v_x_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4452_, v_x_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4458_, lean_object* v_attrName_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v___x_4463_; lean_object* v_env_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4463_ = lean_st_ref_get(v_a_4461_);
v_env_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc_ref(v_env_4464_);
lean_dec(v___x_4463_);
v___x_4465_ = l_Lean_getAttributeImpl(v_env_4464_, v_attrName_4459_);
v___x_4466_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4465_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v_erase_4468_; lean_object* v___x_4469_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v_erase_4468_ = lean_ctor_get(v_a_4467_, 2);
lean_inc_ref(v_erase_4468_);
lean_dec(v_a_4467_);
lean_inc(v_a_4461_);
lean_inc_ref(v_a_4460_);
v___x_4469_ = lean_apply_4(v_erase_4468_, v_declName_4458_, v_a_4460_, v_a_4461_, lean_box(0));
return v___x_4469_;
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_declName_4458_);
v_a_4470_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4466_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4466_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4478_, lean_object* v_attrName_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_Attribute_erase(v_declName_4478_, v_attrName_4479_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4484_, lean_object* v_x_4485_){
_start:
{
if (lean_obj_tag(v_x_4485_) == 0)
{
return v_x_4484_;
}
else
{
lean_object* v_key_4486_; lean_object* v_value_4487_; lean_object* v_tail_4488_; lean_object* v_newEntries_4489_; lean_object* v_map_4490_; uint8_t v___x_4491_; 
v_key_4486_ = lean_ctor_get(v_x_4485_, 0);
lean_inc(v_key_4486_);
v_value_4487_ = lean_ctor_get(v_x_4485_, 1);
lean_inc(v_value_4487_);
v_tail_4488_ = lean_ctor_get(v_x_4485_, 2);
lean_inc(v_tail_4488_);
lean_dec_ref_known(v_x_4485_, 3);
v_newEntries_4489_ = lean_ctor_get(v_x_4484_, 0);
v_map_4490_ = lean_ctor_get(v_x_4484_, 1);
v___x_4491_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4490_, v_key_4486_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4500_; 
lean_inc_ref(v_map_4490_);
lean_inc(v_newEntries_4489_);
v_isSharedCheck_4500_ = !lean_is_exclusive(v_x_4484_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; lean_object* v_unused_4502_; 
v_unused_4501_ = lean_ctor_get(v_x_4484_, 1);
lean_dec(v_unused_4501_);
v_unused_4502_ = lean_ctor_get(v_x_4484_, 0);
lean_dec(v_unused_4502_);
v___x_4493_ = v_x_4484_;
v_isShared_4494_ = v_isSharedCheck_4500_;
goto v_resetjp_4492_;
}
else
{
lean_dec(v_x_4484_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4500_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4490_, v_key_4486_, v_value_4487_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 1, v___x_4495_);
v___x_4497_ = v___x_4493_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_newEntries_4489_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
v_x_4484_ = v___x_4497_;
v_x_4485_ = v_tail_4488_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4487_);
lean_dec(v_key_4486_);
v_x_4485_ = v_tail_4488_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4504_, size_t v_i_4505_, size_t v_stop_4506_, lean_object* v_b_4507_){
_start:
{
uint8_t v___x_4508_; 
v___x_4508_ = lean_usize_dec_eq(v_i_4505_, v_stop_4506_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; size_t v___x_4511_; size_t v___x_4512_; 
v___x_4509_ = lean_array_uget_borrowed(v_as_4504_, v_i_4505_);
lean_inc(v___x_4509_);
v___x_4510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4507_, v___x_4509_);
v___x_4511_ = ((size_t)1ULL);
v___x_4512_ = lean_usize_add(v_i_4505_, v___x_4511_);
v_i_4505_ = v___x_4512_;
v_b_4507_ = v___x_4510_;
goto _start;
}
else
{
return v_b_4507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4514_, lean_object* v_i_4515_, lean_object* v_stop_4516_, lean_object* v_b_4517_){
_start:
{
size_t v_i_boxed_4518_; size_t v_stop_boxed_4519_; lean_object* v_res_4520_; 
v_i_boxed_4518_ = lean_unbox_usize(v_i_4515_);
lean_dec(v_i_4515_);
v_stop_boxed_4519_ = lean_unbox_usize(v_stop_4516_);
lean_dec(v_stop_4516_);
v_res_4520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4514_, v_i_boxed_4518_, v_stop_boxed_4519_, v_b_4517_);
lean_dec_ref(v_as_4514_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4521_){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___y_4528_; lean_object* v_toEnvExtension_4531_; lean_object* v_asyncMode_4532_; lean_object* v_buckets_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v___x_4523_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4524_ = l_Lean_attributeMapRef;
v___x_4525_ = lean_st_ref_get(v___x_4524_);
v___x_4526_ = l_Lean_attributeExtension;
v_toEnvExtension_4531_ = lean_ctor_get(v___x_4526_, 0);
v_asyncMode_4532_ = lean_ctor_get(v_toEnvExtension_4531_, 2);
v_buckets_4533_ = lean_ctor_get(v___x_4525_, 1);
lean_inc_ref(v_buckets_4533_);
lean_dec(v___x_4525_);
v___x_4534_ = lean_box(0);
lean_inc_ref(v_env_4521_);
v___x_4535_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4523_, v___x_4526_, v_env_4521_, v_asyncMode_4532_, v___x_4534_);
v___x_4536_ = lean_unsigned_to_nat(0u);
v___x_4537_ = lean_array_get_size(v_buckets_4533_);
v___x_4538_ = lean_nat_dec_lt(v___x_4536_, v___x_4537_);
if (v___x_4538_ == 0)
{
lean_dec_ref(v_buckets_4533_);
v___y_4528_ = v___x_4535_;
goto v___jp_4527_;
}
else
{
size_t v___x_4539_; size_t v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = ((size_t)0ULL);
v___x_4540_ = lean_usize_of_nat(v___x_4537_);
v___x_4541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4533_, v___x_4539_, v___x_4540_, v___x_4535_);
lean_dec_ref(v_buckets_4533_);
v___y_4528_ = v___x_4541_;
goto v___jp_4527_;
}
v___jp_4527_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4526_, v_env_4521_, v___y_4528_);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = lean_update_env_attributes(v_env_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v_size_4548_; lean_object* v___x_4549_; 
v___x_4546_ = l_Lean_attributeMapRef;
v___x_4547_ = lean_st_ref_get(v___x_4546_);
v_size_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_size_4548_);
lean_dec(v___x_4547_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_size_4548_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = lean_get_num_attributes();
return v_res_4551_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedAttributeApplicationTime_default = _init_l_Lean_instInhabitedAttributeApplicationTime_default();
l_Lean_instInhabitedAttributeApplicationTime = _init_l_Lean_instInhabitedAttributeApplicationTime();
l_Lean_instInhabitedAttributeKind_default = _init_l_Lean_instInhabitedAttributeKind_default();
l_Lean_instInhabitedAttributeKind = _init_l_Lean_instInhabitedAttributeKind();
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeMapRef);
lean_dec_ref(res);
l_Lean_instInhabitedTagAttribute_default = _init_l_Lean_instInhabitedTagAttribute_default();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute_default);
l_Lean_instInhabitedTagAttribute = _init_l_Lean_instInhabitedTagAttribute();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeImplBuilderTableRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeImplBuilderTableRef);
lean_dec_ref(res);
l_Lean_instInhabitedAttributeExtensionState_default = _init_l_Lean_instInhabitedAttributeExtensionState_default();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState_default);
l_Lean_instInhabitedAttributeExtensionState = _init_l_Lean_instInhabitedAttributeExtensionState();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_AttributeImplCore_ref___autoParam = _init_l_Lean_AttributeImplCore_ref___autoParam();
lean_mark_persistent(l_Lean_AttributeImplCore_ref___autoParam);
l_Lean_registerTagAttribute___auto__1 = _init_l_Lean_registerTagAttribute___auto__1();
lean_mark_persistent(l_Lean_registerTagAttribute___auto__1);
l_Lean_registerEnumAttributes___auto__1 = _init_l_Lean_registerEnumAttributes___auto__1();
lean_mark_persistent(l_Lean_registerEnumAttributes___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif
