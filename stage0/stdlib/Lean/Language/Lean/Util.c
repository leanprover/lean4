// Lean compiler output
// Module: Lean.Language.Lean.Util
// Imports: public import Lean.Language.Lean.Types import Lean.Elab.InfoTree.Util
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
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(lean_object*);
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Language.Lean.Util"};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0_value;
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Language.Lean.findCmdDataAtPos"};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1_value;
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: s.infoTree\?.isSome\n        "};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(lean_object*);
static lean_once_cell_t l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___lam__0(lean_object*);
static const lean_closure_object l_Lean_Language_Lean_findInfoTreeAtPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_findInfoTreeAtPos___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___closed__0 = (const lean_object*)&l_Lean_Language_Lean_findInfoTreeAtPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object* v_text_1_, lean_object* v_r_2_, lean_object* v_hoverPos_3_, uint8_t v_includeStop_4_){
_start:
{
if (v_includeStop_4_ == 0)
{
lean_object* v_stop_5_; lean_object* v_source_6_; lean_object* v___x_7_; uint8_t v_decide_8_; uint8_t v___x_9_; 
v_stop_5_ = lean_ctor_get(v_r_2_, 1);
v_source_6_ = lean_ctor_get(v_text_1_, 0);
v___x_7_ = lean_string_utf8_byte_size(v_source_6_);
v_decide_8_ = lean_nat_dec_eq(v_stop_5_, v___x_7_);
v___x_9_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_decide_8_);
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_includeStop_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT void l_Lean_FileMap_rangeContainsHoverPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_1_ = stack[0].m_obj;
lean_object* v_r_2_ = stack[1].m_obj;
lean_object* v_hoverPos_3_ = stack[2].m_obj;
uint8_t v_includeStop_4_ = stack[3].m_num;
uint8_t v_res_11_;
v_res_11_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_1_, v_r_2_, v_hoverPos_3_, v_includeStop_4_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object* v_text_12_, lean_object* v_r_13_, lean_object* v_hoverPos_14_, lean_object* v_includeStop_15_){
_start:
{
uint8_t v_includeStop_boxed_16_; uint8_t v_res_17_; lean_object* v_r_18_; 
v_includeStop_boxed_16_ = lean_unbox(v_includeStop_15_);
v_res_17_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_12_, v_r_13_, v_hoverPos_14_, v_includeStop_boxed_16_);
lean_dec(v_hoverPos_14_);
lean_dec_ref(v_r_13_);
lean_dec_ref(v_text_12_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object* v_text_19_, lean_object* v_documentRange_20_, lean_object* v_requestedRange_21_, uint8_t v_includeDocumentRangeStop_22_, uint8_t v_includeRequestedRangeStop_23_){
_start:
{
if (v_includeDocumentRangeStop_22_ == 0)
{
lean_object* v_stop_24_; lean_object* v_source_25_; lean_object* v___x_26_; uint8_t v_decide_27_; uint8_t v___x_28_; 
v_stop_24_ = lean_ctor_get(v_documentRange_20_, 1);
v_source_25_ = lean_ctor_get(v_text_19_, 0);
v___x_26_ = lean_string_utf8_byte_size(v_source_25_);
v_decide_27_ = lean_nat_dec_eq(v_stop_24_, v___x_26_);
v___x_28_ = l_Lean_Syntax_Range_overlaps(v_documentRange_20_, v_requestedRange_21_, v_decide_27_, v_includeRequestedRangeStop_23_);
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_Lean_Syntax_Range_overlaps(v_documentRange_20_, v_requestedRange_21_, v_includeDocumentRangeStop_22_, v_includeRequestedRangeStop_23_);
return v___x_29_;
}
}
}
LEAN_EXPORT void l_Lean_FileMap_rangeOverlapsRequestedRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_19_ = stack[0].m_obj;
lean_object* v_documentRange_20_ = stack[1].m_obj;
lean_object* v_requestedRange_21_ = stack[2].m_obj;
uint8_t v_includeDocumentRangeStop_22_ = stack[3].m_num;
uint8_t v_includeRequestedRangeStop_23_ = stack[4].m_num;
uint8_t v_res_30_;
v_res_30_ = l_Lean_FileMap_rangeOverlapsRequestedRange(v_text_19_, v_documentRange_20_, v_requestedRange_21_, v_includeDocumentRangeStop_22_, v_includeRequestedRangeStop_23_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object* v_text_31_, lean_object* v_documentRange_32_, lean_object* v_requestedRange_33_, lean_object* v_includeDocumentRangeStop_34_, lean_object* v_includeRequestedRangeStop_35_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_36_; uint8_t v_includeRequestedRangeStop_boxed_37_; uint8_t v_res_38_; lean_object* v_r_39_; 
v_includeDocumentRangeStop_boxed_36_ = lean_unbox(v_includeDocumentRangeStop_34_);
v_includeRequestedRangeStop_boxed_37_ = lean_unbox(v_includeRequestedRangeStop_35_);
v_res_38_ = l_Lean_FileMap_rangeOverlapsRequestedRange(v_text_31_, v_documentRange_32_, v_requestedRange_33_, v_includeDocumentRangeStop_boxed_36_, v_includeRequestedRangeStop_boxed_37_);
lean_dec_ref(v_requestedRange_33_);
lean_dec_ref(v_documentRange_32_);
lean_dec_ref(v_text_31_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object* v_text_40_, lean_object* v_documentRange_41_, lean_object* v_requestedRange_42_, uint8_t v_includeDocumentRangeStop_43_, uint8_t v_includeRequestedRangeStop_44_){
_start:
{
if (v_includeDocumentRangeStop_43_ == 0)
{
lean_object* v_stop_45_; lean_object* v_source_46_; lean_object* v___x_47_; uint8_t v_decide_48_; uint8_t v___x_49_; 
v_stop_45_ = lean_ctor_get(v_documentRange_41_, 1);
v_source_46_ = lean_ctor_get(v_text_40_, 0);
v___x_47_ = lean_string_utf8_byte_size(v_source_46_);
v_decide_48_ = lean_nat_dec_eq(v_stop_45_, v___x_47_);
v___x_49_ = l_Lean_Syntax_Range_includes(v_documentRange_41_, v_requestedRange_42_, v_decide_48_, v_includeRequestedRangeStop_44_);
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = l_Lean_Syntax_Range_includes(v_documentRange_41_, v_requestedRange_42_, v_includeDocumentRangeStop_43_, v_includeRequestedRangeStop_44_);
return v___x_50_;
}
}
}
LEAN_EXPORT void l_Lean_FileMap_rangeIncludesRequestedRange_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_40_ = stack[0].m_obj;
lean_object* v_documentRange_41_ = stack[1].m_obj;
lean_object* v_requestedRange_42_ = stack[2].m_obj;
uint8_t v_includeDocumentRangeStop_43_ = stack[3].m_num;
uint8_t v_includeRequestedRangeStop_44_ = stack[4].m_num;
uint8_t v_res_51_;
v_res_51_ = l_Lean_FileMap_rangeIncludesRequestedRange(v_text_40_, v_documentRange_41_, v_requestedRange_42_, v_includeDocumentRangeStop_43_, v_includeRequestedRangeStop_44_);
stack->m_num = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object* v_text_52_, lean_object* v_documentRange_53_, lean_object* v_requestedRange_54_, lean_object* v_includeDocumentRangeStop_55_, lean_object* v_includeRequestedRangeStop_56_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_57_; uint8_t v_includeRequestedRangeStop_boxed_58_; uint8_t v_res_59_; lean_object* v_r_60_; 
v_includeDocumentRangeStop_boxed_57_ = lean_unbox(v_includeDocumentRangeStop_55_);
v_includeRequestedRangeStop_boxed_58_ = lean_unbox(v_includeRequestedRangeStop_56_);
v_res_59_ = l_Lean_FileMap_rangeIncludesRequestedRange(v_text_52_, v_documentRange_53_, v_requestedRange_54_, v_includeDocumentRangeStop_boxed_57_, v_includeRequestedRangeStop_boxed_58_);
lean_dec_ref(v_requestedRange_54_);
lean_dec_ref(v_documentRange_53_);
lean_dec_ref(v_text_52_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___impl(lean_object* v_x_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_tag_nat(v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___impl___boxed(lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___impl(v_x_63_);
lean_dec(v_x_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object* v_t_65_, lean_object* v_k_66_){
_start:
{
if (lean_obj_tag(v_t_65_) == 0)
{
return v_k_66_;
}
else
{
uint8_t v_foldChildren_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_foldChildren_67_ = lean_ctor_get_uint8(v_t_65_, 0);
v___x_68_ = lean_box(v_foldChildren_67_);
v___x_69_ = lean_apply_1(v_k_66_, v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object* v_t_70_, lean_object* v_k_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_70_, v_k_71_);
lean_dec(v_t_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object* v_motive_73_, lean_object* v_ctorIdx_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_k_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_75_, v_k_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object* v_motive_79_, lean_object* v_ctorIdx_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_k_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(v_motive_79_, v_ctorIdx_80_, v_t_81_, v_h_82_, v_k_83_);
lean_dec(v_t_81_);
lean_dec(v_ctorIdx_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object* v_t_85_, lean_object* v_done_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_85_, v_done_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object* v_t_88_, lean_object* v_done_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(v_t_88_, v_done_89_);
lean_dec(v_t_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_done_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_92_, v_done_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_done_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(v_motive_96_, v_t_97_, v_h_98_, v_done_99_);
lean_dec(v_t_97_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object* v_t_101_, lean_object* v_proceed_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_101_, v_proceed_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object* v_t_104_, lean_object* v_proceed_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(v_t_104_, v_proceed_105_);
lean_dec(v_t_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_proceed_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_108_, v_proceed_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_proceed_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(v_motive_112_, v_t_113_, v_h_114_, v_proceed_115_);
lean_dec(v_t_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object* v_f_117_, lean_object* v_tail_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_snd_120_; uint8_t v___x_121_; 
v_snd_120_ = lean_ctor_get(v_x_119_, 1);
v___x_121_ = lean_unbox(v_snd_120_);
if (v___x_121_ == 0)
{
lean_object* v_fst_122_; lean_object* v___x_123_; 
v_fst_122_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_fst_122_);
lean_dec_ref(v_x_119_);
v___x_123_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_117_, v_fst_122_, v_tail_118_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
lean_dec(v_tail_118_);
lean_dec_ref(v_f_117_);
v___x_124_ = lean_task_pure(v_x_119_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object* v_f_125_, lean_object* v_tail_126_, lean_object* v_head_127_, lean_object* v___f_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_snd_130_; 
v_snd_130_ = lean_ctor_get(v_x_129_, 1);
if (lean_obj_tag(v_snd_130_) == 1)
{
uint8_t v_foldChildren_131_; 
v_foldChildren_131_ = lean_ctor_get_uint8(v_snd_130_, 0);
if (v_foldChildren_131_ == 0)
{
lean_object* v_fst_132_; lean_object* v___x_133_; 
lean_dec_ref(v___f_128_);
lean_dec_ref(v_head_127_);
v_fst_132_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v_x_129_);
v___x_133_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_125_, v_fst_132_, v_tail_126_);
return v___x_133_;
}
else
{
lean_object* v_fst_134_; lean_object* v_task_135_; lean_object* v___f_136_; lean_object* v___x_137_; lean_object* v_subtreeTask_138_; lean_object* v___x_139_; 
lean_dec(v_tail_126_);
v_fst_134_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_fst_134_);
lean_dec_ref(v_x_129_);
v_task_135_ = lean_ctor_get(v_head_127_, 3);
lean_inc_ref(v_task_135_);
lean_dec_ref(v_head_127_);
v___f_136_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_136_, 0, v_f_125_);
lean_closure_set(v___f_136_, 1, v_fst_134_);
v___x_137_ = lean_unsigned_to_nat(0u);
v_subtreeTask_138_ = lean_task_bind(v_task_135_, v___f_136_, v___x_137_, v_foldChildren_131_);
v___x_139_ = lean_task_bind(v_subtreeTask_138_, v___f_128_, v___x_137_, v_foldChildren_131_);
return v___x_139_;
}
}
else
{
lean_object* v_fst_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v___f_128_);
lean_dec_ref(v_head_127_);
lean_dec(v_tail_126_);
lean_dec_ref(v_f_125_);
v_fst_140_ = lean_ctor_get(v_x_129_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v_x_129_, 1);
lean_dec(v_unused_151_);
v___x_142_ = v_x_129_;
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_fst_140_);
lean_dec(v_x_129_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = 1;
v___x_145_ = lean_box(v___x_144_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_145_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_140_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_149_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; 
v___x_148_ = lean_task_pure(v___x_147_);
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object* v_f_152_, lean_object* v_acc_153_, lean_object* v_a_154_){
_start:
{
if (lean_obj_tag(v_a_154_) == 0)
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref(v_f_152_);
v___x_155_ = 0;
v___x_156_ = lean_box(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_acc_153_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_task_pure(v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_head_159_; lean_object* v_tail_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; 
v_head_159_ = lean_ctor_get(v_a_154_, 0);
lean_inc_n(v_head_159_, 2);
v_tail_160_ = lean_ctor_get(v_a_154_, 1);
lean_inc_n(v_tail_160_, 2);
lean_dec_ref_known(v_a_154_, 2);
lean_inc_ref_n(v_f_152_, 2);
v___f_161_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_161_, 0, v_f_152_);
lean_closure_set(v___f_161_, 1, v_tail_160_);
v___f_162_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2), 5, 4);
lean_closure_set(v___f_162_, 0, v_f_152_);
lean_closure_set(v___f_162_, 1, v_tail_160_);
lean_closure_set(v___f_162_, 2, v_head_159_);
lean_closure_set(v___f_162_, 3, v___f_161_);
v___x_163_ = lean_apply_2(v_f_152_, v_head_159_, v_acc_153_);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = 1;
v___x_166_ = lean_task_bind(v___x_163_, v___f_162_, v___x_164_, v___x_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object* v_f_167_, lean_object* v_acc_168_, lean_object* v_tree_169_){
_start:
{
lean_object* v_children_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_children_170_ = lean_ctor_get(v_tree_169_, 1);
lean_inc_ref(v_children_170_);
lean_dec_ref(v_tree_169_);
v___x_171_ = lean_array_to_list(v_children_170_);
v___x_172_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_167_, v_acc_168_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object* v_f_173_, lean_object* v_fst_174_, lean_object* v_tree_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_173_, v_fst_174_, v_tree_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object* v_00_u03b1_177_, lean_object* v_f_178_, lean_object* v_acc_179_, lean_object* v_tree_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_178_, v_acc_179_, v_tree_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object* v_00_u03b1_182_, lean_object* v_f_183_, lean_object* v_acc_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_183_, v_acc_184_, v_a_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object* v_x_187_){
_start:
{
lean_object* v_fst_188_; 
v_fst_188_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_fst_188_);
return v_fst_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(v_x_189_);
lean_dec_ref(v_x_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object* v_tree_192_, lean_object* v_init_193_, lean_object* v_f_194_){
_start:
{
lean_object* v___f_195_; lean_object* v_t_196_; lean_object* v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; 
v___f_195_ = ((lean_object*)(l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0));
v_t_196_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_194_, v_init_193_, v_tree_192_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = 1;
v___x_199_ = lean_task_map(v___f_195_, v_t_196_, v___x_197_, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object* v_00_u03b1_200_, lean_object* v_tree_201_, lean_object* v_init_202_, lean_object* v_f_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_201_, v_init_202_, v_f_203_);
return v___x_204_;
}
}
lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t v___x_205_, lean_object* v___x_206_, lean_object* v_tree_207_){
_start:
{
lean_object* v_element_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_221_; 
v_element_208_ = lean_ctor_get(v_tree_207_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v_tree_207_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v_tree_207_, 1);
lean_dec(v_unused_222_);
v___x_210_ = v_tree_207_;
v_isShared_211_ = v_isSharedCheck_221_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_element_208_);
lean_dec(v_tree_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_221_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_infoTree_x3f_212_; 
v_infoTree_x3f_212_ = lean_ctor_get(v_element_208_, 2);
lean_inc(v_infoTree_x3f_212_);
lean_dec_ref(v_element_208_);
if (lean_obj_tag(v_infoTree_x3f_212_) == 1)
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec(v___x_206_);
v___x_213_ = lean_box(0);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_213_);
lean_ctor_set(v___x_210_, 0, v_infoTree_x3f_212_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_infoTree_x3f_212_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
lean_object* v___x_217_; lean_object* v___x_219_; 
lean_dec(v_infoTree_x3f_212_);
v___x_217_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_217_, 0, v___x_205_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_217_);
lean_ctor_set(v___x_210_, 0, v___x_206_);
v___x_219_ = v___x_210_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_205_ = stack[0].m_num;
lean_object* v___x_206_ = stack[1].m_obj;
lean_object* v_tree_207_ = stack[2].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(v___x_205_, v___x_206_, v_tree_207_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v_tree_226_){
_start:
{
uint8_t v___x_408__boxed_227_; lean_object* v_res_228_; 
v___x_408__boxed_227_ = lean_unbox(v___x_224_);
v_res_228_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(v___x_408__boxed_227_, v___x_225_, v_tree_226_);
return v_res_228_;
}
}
lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object* v_text_233_, lean_object* v_hoverPos_234_, uint8_t v_includeStop_235_, lean_object* v___x_236_, lean_object* v_snap_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_stx_x3f_239_; 
v_stx_x3f_239_ = lean_ctor_get(v_snap_237_, 0);
lean_inc(v_stx_x3f_239_);
if (lean_obj_tag(v_stx_x3f_239_) == 1)
{
lean_object* v_task_240_; lean_object* v_val_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_task_240_ = lean_ctor_get(v_snap_237_, 3);
lean_inc_ref(v_task_240_);
lean_dec_ref(v_snap_237_);
v_val_241_ = lean_ctor_get(v_stx_x3f_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v_stx_x3f_239_, 1);
v___x_242_ = 1;
v___x_243_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_241_, v___x_242_);
lean_dec(v_val_241_);
if (lean_obj_tag(v___x_243_) == 1)
{
lean_object* v_val_244_; uint8_t v___x_245_; 
v_val_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v___x_243_, 1);
v___x_245_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_233_, v_val_244_, v_hoverPos_234_, v_includeStop_235_);
lean_dec(v_val_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_task_240_);
v___x_246_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_246_, 0, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_236_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_task_pure(v___x_247_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_249_ = lean_box(v___x_245_);
v___f_250_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed), 3, 2);
lean_closure_set(v___f_250_, 0, v___x_249_);
lean_closure_set(v___f_250_, 1, v___x_236_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_task_map(v___f_250_, v_task_240_, v___x_251_, v___x_245_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v___x_243_);
lean_dec_ref(v_task_240_);
v___x_253_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_236_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_task_pure(v___x_254_);
return v___x_255_;
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v_stx_x3f_239_);
lean_dec_ref(v_snap_237_);
v___x_256_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_236_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_task_pure(v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_233_ = stack[0].m_obj;
lean_object* v_hoverPos_234_ = stack[1].m_obj;
uint8_t v_includeStop_235_ = stack[2].m_num;
lean_object* v___x_236_ = stack[3].m_obj;
lean_object* v_snap_237_ = stack[4].m_obj;
lean_object* v_x_238_ = stack[5].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(v_text_233_, v_hoverPos_234_, v_includeStop_235_, v___x_236_, v_snap_237_, v_x_238_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object* v_text_260_, lean_object* v_hoverPos_261_, lean_object* v_includeStop_262_, lean_object* v___x_263_, lean_object* v_snap_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_includeStop_boxed_266_; lean_object* v_res_267_; 
v_includeStop_boxed_266_ = lean_unbox(v_includeStop_262_);
v_res_267_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(v_text_260_, v_hoverPos_261_, v_includeStop_boxed_266_, v___x_263_, v_snap_264_, v_x_265_);
lean_dec(v_x_265_);
lean_dec(v_hoverPos_261_);
lean_dec_ref(v_text_260_);
return v_res_267_;
}
}
lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object* v_text_268_, lean_object* v_tree_269_, lean_object* v_hoverPos_270_, uint8_t v_includeStop_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___x_272_ = lean_box(0);
v___x_273_ = lean_box(v_includeStop_271_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed), 6, 4);
lean_closure_set(v___f_274_, 0, v_text_268_);
lean_closure_set(v___f_274_, 1, v_hoverPos_270_);
lean_closure_set(v___f_274_, 2, v___x_273_);
lean_closure_set(v___f_274_, 3, v___x_272_);
v___x_275_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_269_, v___x_272_, v___f_274_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_findInfoTreeAtPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_268_ = stack[0].m_obj;
lean_object* v_tree_269_ = stack[1].m_obj;
lean_object* v_hoverPos_270_ = stack[2].m_obj;
uint8_t v_includeStop_271_ = stack[3].m_num;
lean_object* v_res_276_;
v_res_276_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_268_, v_tree_269_, v_hoverPos_270_, v_includeStop_271_);
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object* v_text_277_, lean_object* v_tree_278_, lean_object* v_hoverPos_279_, lean_object* v_includeStop_280_){
_start:
{
uint8_t v_includeStop_boxed_281_; lean_object* v_res_282_; 
v_includeStop_boxed_281_ = lean_unbox(v_includeStop_280_);
v_res_282_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_277_, v_tree_278_, v_hoverPos_279_, v_includeStop_boxed_281_);
return v_res_282_;
}
}
lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object* v_requestedRange_283_, uint8_t v___x_284_, lean_object* v_f_285_, lean_object* v_ctx_286_, lean_object* v_i_287_, lean_object* v_acc_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Elab_Info_range_x3f(v_i_287_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; uint8_t v___x_291_; 
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec_ref_known(v___x_289_, 1);
v___x_291_ = l_Lean_Syntax_Range_overlaps(v_val_290_, v_requestedRange_283_, v___x_284_, v___x_284_);
lean_dec(v_val_290_);
if (v___x_291_ == 0)
{
lean_dec_ref(v_i_287_);
lean_dec_ref(v_ctx_286_);
lean_dec(v_f_285_);
return v_acc_288_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_apply_3(v_f_285_, v_ctx_286_, v_i_287_, v_acc_288_);
return v___x_292_;
}
}
else
{
lean_dec(v___x_289_);
lean_dec_ref(v_i_287_);
lean_dec_ref(v_ctx_286_);
lean_dec(v_f_285_);
return v_acc_288_;
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestedRange_283_ = stack[0].m_obj;
uint8_t v___x_284_ = stack[1].m_num;
lean_object* v_f_285_ = stack[2].m_obj;
lean_object* v_ctx_286_ = stack[3].m_obj;
lean_object* v_i_287_ = stack[4].m_obj;
lean_object* v_acc_288_ = stack[5].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(v_requestedRange_283_, v___x_284_, v_f_285_, v_ctx_286_, v_i_287_, v_acc_288_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object* v_requestedRange_294_, lean_object* v___x_295_, lean_object* v_f_296_, lean_object* v_ctx_297_, lean_object* v_i_298_, lean_object* v_acc_299_){
_start:
{
uint8_t v___x_559__boxed_300_; lean_object* v_res_301_; 
v___x_559__boxed_300_ = lean_unbox(v___x_295_);
v_res_301_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(v_requestedRange_294_, v___x_559__boxed_300_, v_f_296_, v_ctx_297_, v_i_298_, v_acc_299_);
lean_dec_ref(v_requestedRange_294_);
return v_res_301_;
}
}
lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object* v___f_302_, lean_object* v_acc_303_, uint8_t v___x_304_, lean_object* v_tree_305_){
_start:
{
lean_object* v_element_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_321_; 
v_element_306_ = lean_ctor_get(v_tree_305_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_tree_305_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_tree_305_, 1);
lean_dec(v_unused_322_);
v___x_308_ = v_tree_305_;
v_isShared_309_ = v_isSharedCheck_321_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_element_306_);
lean_dec(v_tree_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_321_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_infoTree_x3f_310_; 
v_infoTree_x3f_310_ = lean_ctor_get(v_element_306_, 2);
lean_inc(v_infoTree_x3f_310_);
lean_dec_ref(v_element_306_);
if (lean_obj_tag(v_infoTree_x3f_310_) == 1)
{
lean_object* v_val_311_; lean_object* v_acc_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_val_311_ = lean_ctor_get(v_infoTree_x3f_310_, 0);
lean_inc(v_val_311_);
lean_dec_ref_known(v_infoTree_x3f_310_, 1);
v_acc_312_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_302_, v_acc_303_, v_val_311_);
v___x_313_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_313_, 0, v___x_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_313_);
lean_ctor_set(v___x_308_, 0, v_acc_312_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_acc_312_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec(v_infoTree_x3f_310_);
lean_dec(v___f_302_);
v___x_317_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_317_, 0, v___x_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_317_);
lean_ctor_set(v___x_308_, 0, v_acc_303_);
v___x_319_ = v___x_308_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_acc_303_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_302_ = stack[0].m_obj;
lean_object* v_acc_303_ = stack[1].m_obj;
uint8_t v___x_304_ = stack[2].m_num;
lean_object* v_tree_305_ = stack[3].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(v___f_302_, v_acc_303_, v___x_304_, v_tree_305_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object* v___f_324_, lean_object* v_acc_325_, lean_object* v___x_326_, lean_object* v_tree_327_){
_start:
{
uint8_t v___x_577__boxed_328_; lean_object* v_res_329_; 
v___x_577__boxed_328_ = lean_unbox(v___x_326_);
v_res_329_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(v___f_324_, v_acc_325_, v___x_577__boxed_328_, v_tree_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object* v_requestedRange_330_, lean_object* v_f_331_, lean_object* v_snap_332_, lean_object* v_acc_333_){
_start:
{
lean_object* v_stx_x3f_334_; 
v_stx_x3f_334_ = lean_ctor_get(v_snap_332_, 0);
lean_inc(v_stx_x3f_334_);
if (lean_obj_tag(v_stx_x3f_334_) == 1)
{
lean_object* v_task_335_; lean_object* v_val_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v_task_335_ = lean_ctor_get(v_snap_332_, 3);
lean_inc_ref(v_task_335_);
lean_dec_ref(v_snap_332_);
v_val_336_ = lean_ctor_get(v_stx_x3f_334_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v_stx_x3f_334_, 1);
v___x_337_ = 1;
v___x_338_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_336_, v___x_337_);
lean_dec(v_val_336_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v_val_339_; uint8_t v___x_340_; 
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v___x_338_, 1);
v___x_340_ = l_Lean_Syntax_Range_overlaps(v_val_339_, v_requestedRange_330_, v___x_337_, v___x_337_);
lean_dec(v_val_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec_ref(v_task_335_);
lean_dec(v_f_331_);
lean_dec_ref(v_requestedRange_330_);
v___x_341_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_acc_333_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_task_pure(v___x_342_);
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = lean_box(v___x_337_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_345_, 0, v_requestedRange_330_);
lean_closure_set(v___f_345_, 1, v___x_344_);
lean_closure_set(v___f_345_, 2, v_f_331_);
v___x_346_ = lean_box(v___x_337_);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_347_, 0, v___f_345_);
lean_closure_set(v___f_347_, 1, v_acc_333_);
lean_closure_set(v___f_347_, 2, v___x_346_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_task_map(v___f_347_, v_task_335_, v___x_348_, v___x_337_);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v___x_338_);
lean_dec_ref(v_task_335_);
lean_dec(v_f_331_);
lean_dec_ref(v_requestedRange_330_);
v___x_350_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_acc_333_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = lean_task_pure(v___x_351_);
return v___x_352_;
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_stx_x3f_334_);
lean_dec_ref(v_snap_332_);
lean_dec(v_f_331_);
lean_dec_ref(v_requestedRange_330_);
v___x_353_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_acc_333_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_task_pure(v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object* v_tree_356_, lean_object* v_requestedRange_357_, lean_object* v_init_358_, lean_object* v_f_359_){
_start:
{
lean_object* v___f_360_; lean_object* v___x_361_; 
v___f_360_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2), 4, 2);
lean_closure_set(v___f_360_, 0, v_requestedRange_357_);
lean_closure_set(v___f_360_, 1, v_f_359_);
v___x_361_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_356_, v_init_358_, v___f_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object* v_00_u03b1_362_, lean_object* v_tree_363_, lean_object* v_requestedRange_364_, lean_object* v_init_365_, lean_object* v_f_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_363_, v_requestedRange_364_, v_init_365_, v_f_366_);
return v___x_367_;
}
}
lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object* v_log_368_, uint8_t v___x_369_, lean_object* v_tree_370_){
_start:
{
lean_object* v_element_371_; lean_object* v_diagnostics_372_; lean_object* v_msgLog_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
v_element_371_ = lean_ctor_get(v_tree_370_, 0);
lean_inc_ref(v_element_371_);
lean_dec_ref(v_tree_370_);
v_diagnostics_372_ = lean_ctor_get(v_element_371_, 1);
lean_inc_ref(v_diagnostics_372_);
lean_dec_ref(v_element_371_);
v_msgLog_373_ = lean_ctor_get(v_diagnostics_372_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_diagnostics_372_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_diagnostics_372_, 1);
lean_dec(v_unused_383_);
v___x_375_ = v_diagnostics_372_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_msgLog_373_);
lean_dec(v_diagnostics_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = l_Lean_MessageLog_append(v_log_368_, v_msgLog_373_);
v___x_378_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_378_, 0, v___x_369_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v___x_378_);
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
LEAN_EXPORT void l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_368_ = stack[0].m_obj;
uint8_t v___x_369_ = stack[1].m_num;
lean_object* v_tree_370_ = stack[2].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(v_log_368_, v___x_369_, v_tree_370_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object* v_log_385_, lean_object* v___x_386_, lean_object* v_tree_387_){
_start:
{
uint8_t v___x_385__boxed_388_; lean_object* v_res_389_; 
v___x_385__boxed_388_ = lean_unbox(v___x_386_);
v_res_389_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(v_log_385_, v___x_385__boxed_388_, v_tree_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object* v_requestedRange_390_, lean_object* v_snap_391_, lean_object* v_log_392_){
_start:
{
lean_object* v_stx_x3f_393_; 
v_stx_x3f_393_ = lean_ctor_get(v_snap_391_, 0);
lean_inc(v_stx_x3f_393_);
if (lean_obj_tag(v_stx_x3f_393_) == 1)
{
lean_object* v_task_394_; lean_object* v_val_395_; uint8_t v___x_396_; lean_object* v___x_397_; 
v_task_394_ = lean_ctor_get(v_snap_391_, 3);
lean_inc_ref(v_task_394_);
lean_dec_ref(v_snap_391_);
v_val_395_ = lean_ctor_get(v_stx_x3f_393_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_stx_x3f_393_, 1);
v___x_396_ = 1;
v___x_397_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_395_, v___x_396_);
lean_dec(v_val_395_);
if (lean_obj_tag(v___x_397_) == 1)
{
lean_object* v_val_398_; uint8_t v___x_399_; 
v_val_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = l_Lean_Syntax_Range_overlaps(v_val_398_, v_requestedRange_390_, v___x_396_, v___x_396_);
lean_dec(v_val_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v_task_394_);
v___x_400_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_400_, 0, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_log_392_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_task_pure(v___x_401_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_box(v___x_396_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed), 3, 2);
lean_closure_set(v___f_404_, 0, v_log_392_);
lean_closure_set(v___f_404_, 1, v___x_403_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_task_map(v___f_404_, v_task_394_, v___x_405_, v___x_396_);
return v___x_406_;
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v___x_397_);
lean_dec_ref(v_task_394_);
v___x_407_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_log_392_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_task_pure(v___x_408_);
return v___x_409_;
}
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec(v_stx_x3f_393_);
lean_dec_ref(v_snap_391_);
v___x_410_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_log_392_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_task_pure(v___x_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object* v_requestedRange_413_, lean_object* v_snap_414_, lean_object* v_log_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(v_requestedRange_413_, v_snap_414_, v_log_415_);
lean_dec_ref(v_requestedRange_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object* v_tree_417_, lean_object* v_requestedRange_418_){
_start:
{
lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed), 3, 1);
lean_closure_set(v___f_419_, 0, v_requestedRange_418_);
v___x_420_ = l_Lean_MessageLog_empty;
v___x_421_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_417_, v___x_420_, v___f_419_);
return v___x_421_;
}
}
uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(lean_object* v_hoverPos_422_, lean_object* v_cmdParsed_423_){
_start:
{
lean_object* v_stx_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v_stx_424_ = lean_ctor_get(v_cmdParsed_423_, 1);
v___x_425_ = 1;
v___x_426_ = l_Lean_Syntax_getPos_x3f(v_stx_424_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_hoverPos_422_, v___x_428_);
v___x_430_ = lean_nat_dec_le(v___x_429_, v_val_427_);
lean_dec(v_val_427_);
lean_dec(v___x_429_);
return v___x_430_;
}
else
{
uint8_t v___x_431_; 
lean_dec(v___x_426_);
v___x_431_ = 0;
return v___x_431_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_hoverPos_422_ = stack[0].m_obj;
lean_object* v_cmdParsed_423_ = stack[1].m_obj;
uint8_t v_res_432_;
v_res_432_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_422_, v_cmdParsed_423_);
stack->m_num = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object* v_hoverPos_433_, lean_object* v_cmdParsed_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_433_, v_cmdParsed_434_);
lean_dec_ref(v_cmdParsed_434_);
lean_dec(v_hoverPos_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(lean_object* v_text_437_, lean_object* v_hoverPos_438_, lean_object* v_cmdParsed_439_){
_start:
{
lean_object* v_stx_440_; uint8_t v___x_441_; lean_object* v___x_442_; 
v_stx_440_ = lean_ctor_get(v_cmdParsed_439_, 1);
v___x_441_ = 1;
v___x_442_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_440_, v___x_441_);
if (lean_obj_tag(v___x_442_) == 1)
{
lean_object* v_val_443_; uint8_t v___x_444_; uint8_t v___x_445_; 
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = 0;
v___x_445_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_437_, v_val_443_, v_hoverPos_438_, v___x_444_);
lean_dec(v_val_443_);
return v___x_445_;
}
else
{
uint8_t v___x_446_; 
lean_dec(v___x_442_);
v___x_446_ = 0;
return v___x_446_;
}
}
}
LEAN_EXPORT void l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_437_ = stack[0].m_obj;
lean_object* v_hoverPos_438_ = stack[1].m_obj;
lean_object* v_cmdParsed_439_ = stack[2].m_obj;
uint8_t v_res_447_;
v_res_447_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_437_, v_hoverPos_438_, v_cmdParsed_439_);
stack->m_num = v_res_447_;
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos___boxed(lean_object* v_text_448_, lean_object* v_hoverPos_449_, lean_object* v_cmdParsed_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_448_, v_hoverPos_449_, v_cmdParsed_450_);
lean_dec_ref(v_cmdParsed_450_);
lean_dec(v_hoverPos_449_);
lean_dec_ref(v_text_448_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_task_pure(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go(lean_object* v_text_455_, lean_object* v_hoverPos_456_, lean_object* v_cmdParsed_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_455_, v_hoverPos_456_, v_cmdParsed_457_);
if (v___x_458_ == 0)
{
uint8_t v___x_459_; 
v___x_459_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_456_, v_cmdParsed_457_);
if (v___x_459_ == 0)
{
lean_object* v_nextCmdSnap_x3f_460_; 
v_nextCmdSnap_x3f_460_ = lean_ctor_get(v_cmdParsed_457_, 4);
lean_inc(v_nextCmdSnap_x3f_460_);
lean_dec_ref(v_cmdParsed_457_);
if (lean_obj_tag(v_nextCmdSnap_x3f_460_) == 0)
{
lean_object* v___x_461_; 
lean_dec(v_hoverPos_456_);
lean_dec_ref(v_text_455_);
v___x_461_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_461_;
}
else
{
lean_object* v_val_462_; lean_object* v_task_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_val_462_ = lean_ctor_get(v_nextCmdSnap_x3f_460_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v_nextCmdSnap_x3f_460_, 1);
v_task_463_ = lean_ctor_get(v_val_462_, 3);
lean_inc_ref(v_task_463_);
lean_dec(v_val_462_);
v___x_464_ = 1;
v___x_465_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_465_, 0, v_text_455_);
lean_closure_set(v___x_465_, 1, v_hoverPos_456_);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_task_bind(v_task_463_, v___x_465_, v___x_466_, v___x_464_);
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v_cmdParsed_457_);
lean_dec(v_hoverPos_456_);
lean_dec_ref(v_text_455_);
v___x_468_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_468_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_hoverPos_456_);
lean_dec_ref(v_text_455_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v_cmdParsed_457_);
v___x_470_ = lean_task_pure(v___x_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap___lam__0(lean_object* v_text_471_, lean_object* v_hoverPos_472_, lean_object* v_headerProcessed_473_){
_start:
{
lean_object* v_result_x3f_474_; 
v_result_x3f_474_ = lean_ctor_get(v_headerProcessed_473_, 2);
lean_inc(v_result_x3f_474_);
lean_dec_ref(v_headerProcessed_473_);
if (lean_obj_tag(v_result_x3f_474_) == 1)
{
lean_object* v_val_475_; lean_object* v_firstCmdSnap_476_; lean_object* v_task_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; 
v_val_475_ = lean_ctor_get(v_result_x3f_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v_result_x3f_474_, 1);
v_firstCmdSnap_476_ = lean_ctor_get(v_val_475_, 1);
lean_inc_ref(v_firstCmdSnap_476_);
lean_dec(v_val_475_);
v_task_477_ = lean_ctor_get(v_firstCmdSnap_476_, 3);
lean_inc_ref(v_task_477_);
lean_dec_ref(v_firstCmdSnap_476_);
v___x_478_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_478_, 0, v_text_471_);
lean_closure_set(v___x_478_, 1, v_hoverPos_472_);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = 1;
v___x_481_ = lean_task_bind(v_task_477_, v___x_478_, v___x_479_, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; 
lean_dec(v_result_x3f_474_);
lean_dec(v_hoverPos_472_);
lean_dec_ref(v_text_471_);
v___x_482_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap(lean_object* v_initSnap_483_, lean_object* v_text_484_, lean_object* v_hoverPos_485_){
_start:
{
lean_object* v_result_x3f_486_; 
v_result_x3f_486_ = lean_ctor_get(v_initSnap_483_, 4);
lean_inc(v_result_x3f_486_);
lean_dec_ref(v_initSnap_483_);
if (lean_obj_tag(v_result_x3f_486_) == 1)
{
lean_object* v_val_487_; lean_object* v_processedSnap_488_; lean_object* v_task_489_; lean_object* v___f_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
v_val_487_ = lean_ctor_get(v_result_x3f_486_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v_result_x3f_486_, 1);
v_processedSnap_488_ = lean_ctor_get(v_val_487_, 1);
lean_inc_ref(v_processedSnap_488_);
lean_dec(v_val_487_);
v_task_489_ = lean_ctor_get(v_processedSnap_488_, 3);
lean_inc_ref(v_task_489_);
lean_dec_ref(v_processedSnap_488_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdParsedSnap___lam__0), 3, 2);
lean_closure_set(v___f_490_, 0, v_text_484_);
lean_closure_set(v___f_490_, 1, v_hoverPos_485_);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = 1;
v___x_493_ = lean_task_bind(v_task_489_, v___f_490_, v___x_491_, v___x_492_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
lean_dec(v_result_x3f_486_);
lean_dec(v_hoverPos_485_);
lean_dec_ref(v_text_484_);
v___x_494_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(lean_object* v_msg_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_box(0);
v___x_497_ = lean_panic_fn_borrowed(v___x_496_, v_msg_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_501_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2));
v___x_502_ = lean_unsigned_to_nat(8u);
v___x_503_ = lean_unsigned_to_nat(199u);
v___x_504_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1));
v___x_505_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0));
v___x_506_ = l_mkPanicMessageWithDecl(v___x_505_, v___x_504_, v___x_503_, v___x_502_, v___x_501_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0(lean_object* v_stx_507_, lean_object* v_s_508_){
_start:
{
lean_object* v_infoTree_x3f_509_; 
v_infoTree_x3f_509_ = lean_ctor_get(v_s_508_, 2);
lean_inc(v_infoTree_x3f_509_);
lean_dec_ref(v_s_508_);
if (lean_obj_tag(v_infoTree_x3f_509_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_stx_507_);
v___x_510_ = lean_obj_once(&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3, &l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3_once, _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3);
v___x_511_ = l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_val_512_ = lean_ctor_get(v_infoTree_x3f_509_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v_infoTree_x3f_509_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v_infoTree_x3f_509_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_val_512_);
lean_dec(v_infoTree_x3f_509_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_stx_507_);
lean_ctor_set(v___x_516_, 1, v_val_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__1(lean_object* v_elabSnap_521_, lean_object* v___f_522_, lean_object* v_stx_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v_infoTreeSnap_525_; lean_object* v_task_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; 
lean_dec(v_stx_523_);
v_infoTreeSnap_525_ = lean_ctor_get(v_elabSnap_521_, 3);
lean_inc_ref(v_infoTreeSnap_525_);
lean_dec_ref(v_elabSnap_521_);
v_task_526_ = lean_ctor_get(v_infoTreeSnap_525_, 3);
lean_inc_ref(v_task_526_);
lean_dec_ref(v_infoTreeSnap_525_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = 1;
v___x_529_ = lean_task_map(v___f_522_, v_task_526_, v___x_527_, v___x_528_);
return v___x_529_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v___f_522_);
lean_dec_ref(v_elabSnap_521_);
v_val_530_ = lean_ctor_get(v_x_524_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_524_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v_x_524_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_val_530_);
lean_dec(v_x_524_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_stx_523_);
lean_ctor_set(v___x_534_, 1, v_val_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_task_pure(v___x_536_);
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object* v_s_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_toSnapshot_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_toSnapshot_544_ = lean_ctor_get(v_s_542_, 0);
lean_inc_ref(v_toSnapshot_544_);
lean_dec_ref(v_s_542_);
v___x_545_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_544_, v___y_543_);
v___x_546_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object* v_s_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(v_s_548_, v___y_549_);
lean_dec_ref(v___y_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(lean_object* v_t_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___f_554_; lean_object* v___x_555_; 
v___f_554_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0));
v___x_555_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_552_, v___f_554_, v_a_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object* v_t_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(v_t_556_, v_a_557_);
lean_dec_ref(v_a_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(lean_object* v_t_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___f_562_; lean_object* v___x_563_; 
v___f_562_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0));
v___x_563_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_560_, v___f_562_, v_a_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object* v_t_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(v_t_564_, v_a_565_);
lean_dec_ref(v_a_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object* v_s_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = l_Lean_Language_Snapshot_transform(v_s_567_, v___y_568_);
v___x_570_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object* v_s_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(v_s_572_, v___y_573_);
lean_dec_ref(v___y_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(lean_object* v_t_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___f_578_; lean_object* v___x_579_; 
v___f_578_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0));
v___x_579_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_576_, v___f_578_, v_a_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object* v_t_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(v_t_580_, v_a_581_);
lean_dec_ref(v_a_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object* v_s_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_toSnapshotTreeM_585_; lean_object* v___x_586_; 
v_toSnapshotTreeM_585_ = lean_ctor_get(v_s_583_, 1);
lean_inc_ref(v_toSnapshotTreeM_585_);
lean_dec_ref(v_s_583_);
lean_inc_ref(v___y_584_);
v___x_586_ = lean_apply_1(v_toSnapshotTreeM_585_, v___y_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object* v_s_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(v_s_587_, v___y_588_);
lean_dec_ref(v___y_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(lean_object* v_t_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___f_593_; lean_object* v___x_594_; 
v___f_593_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0));
v___x_594_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_591_, v___f_593_, v_a_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object* v_t_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(v_t_595_, v_a_596_);
lean_dec_ref(v_a_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(lean_object* v_a_598_){
_start:
{
lean_object* v_toSnapshot_599_; lean_object* v_elabSnap_600_; lean_object* v_resultSnap_601_; lean_object* v_infoTreeSnap_602_; lean_object* v_reportSnap_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_toSnapshot_599_ = lean_ctor_get(v_a_598_, 0);
lean_inc_ref(v_toSnapshot_599_);
v_elabSnap_600_ = lean_ctor_get(v_a_598_, 1);
lean_inc_ref(v_elabSnap_600_);
v_resultSnap_601_ = lean_ctor_get(v_a_598_, 2);
lean_inc_ref(v_resultSnap_601_);
v_infoTreeSnap_602_ = lean_ctor_get(v_a_598_, 3);
lean_inc_ref(v_infoTreeSnap_602_);
v_reportSnap_603_ = lean_ctor_get(v_a_598_, 4);
lean_inc_ref(v_reportSnap_603_);
lean_dec_ref(v_a_598_);
v___x_604_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_605_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_599_, v___x_604_);
v___x_606_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(v_elabSnap_600_, v___x_604_);
v___x_607_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(v_resultSnap_601_, v___x_604_);
v___x_608_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(v_infoTreeSnap_602_, v___x_604_);
v___x_609_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(v_reportSnap_603_, v___x_604_);
v___x_610_ = lean_unsigned_to_nat(4u);
v___x_611_ = lean_mk_empty_array_with_capacity(v___x_610_);
v___x_612_ = lean_array_push(v___x_611_, v___x_606_);
v___x_613_ = lean_array_push(v___x_612_, v___x_607_);
v___x_614_ = lean_array_push(v___x_613_, v___x_608_);
v___x_615_ = lean_array_push(v___x_614_, v___x_609_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_605_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_task_pure(v___x_617_);
return v___x_618_;
}
}
lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2(lean_object* v_text_619_, lean_object* v_hoverPos_620_, uint8_t v_includeStop_621_, lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
lean_object* v___x_623_; 
lean_dec(v_hoverPos_620_);
lean_dec_ref(v_text_619_);
v___x_623_ = lean_obj_once(&l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0, &l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0_once, _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0);
return v___x_623_;
}
else
{
lean_object* v_val_624_; lean_object* v_stx_625_; lean_object* v_elabSnap_626_; lean_object* v___f_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; 
v_val_624_ = lean_ctor_get(v_x_622_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_x_622_, 1);
v_stx_625_ = lean_ctor_get(v_val_624_, 1);
lean_inc_n(v_stx_625_, 2);
v_elabSnap_626_ = lean_ctor_get(v_val_624_, 3);
lean_inc_ref_n(v_elabSnap_626_, 2);
lean_dec(v_val_624_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0), 2, 1);
lean_closure_set(v___f_627_, 0, v_stx_625_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__1), 4, 3);
lean_closure_set(v___f_628_, 0, v_elabSnap_626_);
lean_closure_set(v___f_628_, 1, v___f_627_);
lean_closure_set(v___f_628_, 2, v_stx_625_);
v___x_629_ = l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(v_elabSnap_626_);
v___x_630_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_619_, v___x_629_, v_hoverPos_620_, v_includeStop_621_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = 1;
v___x_633_ = lean_task_bind(v___x_630_, v___f_628_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
}
LEAN_EXPORT void l_Lean_Language_Lean_findCmdDataAtPos___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_619_ = stack[0].m_obj;
lean_object* v_hoverPos_620_ = stack[1].m_obj;
uint8_t v_includeStop_621_ = stack[2].m_num;
lean_object* v_x_622_ = stack[3].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_Language_Lean_findCmdDataAtPos___lam__2(v_text_619_, v_hoverPos_620_, v_includeStop_621_, v_x_622_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed(lean_object* v_text_635_, lean_object* v_hoverPos_636_, lean_object* v_includeStop_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_includeStop_boxed_639_; lean_object* v_res_640_; 
v_includeStop_boxed_639_ = lean_unbox(v_includeStop_637_);
v_res_640_ = l_Lean_Language_Lean_findCmdDataAtPos___lam__2(v_text_635_, v_hoverPos_636_, v_includeStop_boxed_639_, v_x_638_);
return v_res_640_;
}
}
lean_object* l_Lean_Language_Lean_findCmdDataAtPos(lean_object* v_initSnap_641_, lean_object* v_text_642_, lean_object* v_hoverPos_643_, uint8_t v_includeStop_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___f_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; 
v___x_645_ = lean_box(v_includeStop_644_);
lean_inc(v_hoverPos_643_);
lean_inc_ref(v_text_642_);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed), 4, 3);
lean_closure_set(v___f_646_, 0, v_text_642_);
lean_closure_set(v___f_646_, 1, v_hoverPos_643_);
lean_closure_set(v___f_646_, 2, v___x_645_);
v___x_647_ = l_Lean_Language_Lean_findCmdParsedSnap(v_initSnap_641_, v_text_642_, v_hoverPos_643_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = 1;
v___x_650_ = lean_task_bind(v___x_647_, v___f_646_, v___x_648_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT void l_Lean_Language_Lean_findCmdDataAtPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_initSnap_641_ = stack[0].m_obj;
lean_object* v_text_642_ = stack[1].m_obj;
lean_object* v_hoverPos_643_ = stack[2].m_obj;
uint8_t v_includeStop_644_ = stack[3].m_num;
lean_object* v_res_651_;
v_res_651_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_641_, v_text_642_, v_hoverPos_643_, v_includeStop_644_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___boxed(lean_object* v_initSnap_652_, lean_object* v_text_653_, lean_object* v_hoverPos_654_, lean_object* v_includeStop_655_){
_start:
{
uint8_t v_includeStop_boxed_656_; lean_object* v_res_657_; 
v_includeStop_boxed_656_ = lean_unbox(v_includeStop_655_);
v_res_657_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_652_, v_text_653_, v_hoverPos_654_, v_includeStop_boxed_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___lam__0(lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_box(0);
return v___x_659_;
}
else
{
lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_val_660_ = lean_ctor_get(v_x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v_x_658_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v_x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_snd_664_; lean_object* v___x_666_; 
v_snd_664_ = lean_ctor_get(v_val_660_, 1);
lean_inc(v_snd_664_);
lean_dec(v_val_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v_snd_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_snd_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object* v_initSnap_670_, lean_object* v_text_671_, lean_object* v_hoverPos_672_, uint8_t v_includeStop_673_){
_start:
{
lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; 
v___f_674_ = ((lean_object*)(l_Lean_Language_Lean_findInfoTreeAtPos___closed__0));
v___x_675_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_670_, v_text_671_, v_hoverPos_672_, v_includeStop_673_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = 1;
v___x_678_ = lean_task_map(v___f_674_, v___x_675_, v___x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT void l_Lean_Language_Lean_findInfoTreeAtPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_initSnap_670_ = stack[0].m_obj;
lean_object* v_text_671_ = stack[1].m_obj;
lean_object* v_hoverPos_672_ = stack[2].m_obj;
uint8_t v_includeStop_673_ = stack[3].m_num;
lean_object* v_res_679_;
v_res_679_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_670_, v_text_671_, v_hoverPos_672_, v_includeStop_673_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___boxed(lean_object* v_initSnap_680_, lean_object* v_text_681_, lean_object* v_hoverPos_682_, lean_object* v_includeStop_683_){
_start:
{
uint8_t v_includeStop_boxed_684_; lean_object* v_res_685_; 
v_includeStop_boxed_684_ = lean_unbox(v_includeStop_683_);
v_res_685_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_680_, v_text_681_, v_hoverPos_682_, v_includeStop_boxed_684_);
return v_res_685_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Lean_Util(builtin);
}
#ifdef __cplusplus
}
#endif
