// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search import Lake.Util.String
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lake_isHex(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__1 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRev_head___closed__0 = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_head = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
static const lean_string_object l_Lake_GitRev_fetchHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FETCH_HEAD"};
static const lean_object* l_Lake_GitRev_fetchHead___closed__0 = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_fetchHead = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_withRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRev_withRemote___closed__0 = (const lean_object*)&l_Lake_GitRev_withRemote___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_GitRepo_instCoeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_GitRepo_instCoeFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_GitRepo_instCoeFilePath___closed__0 = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instCoeFilePath = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instToString = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_gitExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_gitExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdout:\n"};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0_value;
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "failed to execute 'git': "};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_bareInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--bare"};
static const lean_object* l_Lake_GitRepo_bareInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_bareInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_bareInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "worktree"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__1_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__2 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__3;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__4;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_gcAuto___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gc"};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__0 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__0_value;
static const lean_string_object l_Lake_GitRepo_gcAuto___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--auto"};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__1 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__1_value;
static const lean_array_object l_Lake_GitRepo_gcAuto___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_gcAuto___closed__0_value),((lean_object*)&l_Lake_GitRepo_gcAuto___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__2 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findCommit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_findCommit_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findCommit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--filter=tree:0"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__1;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__4;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = ": could not resolve 'FETCH_HEAD' to a commit after fetching; this may be an issue with Lake; please report it"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__5 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__0;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__0;
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_setRemoteUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "set-url"};
static const lean_object* l_Lake_GitRepo_setRemoteUrl___closed__0 = (const lean_object*)&l_Lake_GitRepo_setRemoteUrl___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_setRemoteUrl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_setRemoteUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_pruneRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "prune"};
static const lean_object* l_Lake_GitRepo_pruneRemote___closed__0 = (const lean_object*)&l_Lake_GitRepo_pruneRemote___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_pruneRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_pruneRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_7_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_string_utf8_byte_size(v_url_7_);
v___x_23_ = lean_unsigned_to_nat(3u);
v___x_24_ = lean_nat_dec_le(v___x_23_, v___x_22_);
if (v___x_24_ == 0)
{
goto v___jp_8_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_25_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_string_memcmp(v_url_7_, v___x_25_, v___x_26_, v___x_26_, v___x_23_);
if (v___x_27_ == 0)
{
goto v___jp_8_;
}
else
{
lean_object* v___x_28_; 
lean_dec_ref(v_url_7_);
v___x_28_ = lean_box(0);
return v___x_28_;
}
}
v___jp_8_:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_9_ = lean_string_utf8_byte_size(v_url_7_);
v___x_10_ = lean_unsigned_to_nat(4u);
v___x_11_ = lean_nat_dec_le(v___x_10_, v___x_9_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v_url_7_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_sub(v___x_9_, v___x_10_);
v___x_16_ = lean_string_memcmp(v_url_7_, v___x_13_, v___x_15_, v___x_14_, v___x_10_);
lean_dec(v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_7_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_ref(v_url_7_);
v___x_18_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_18_, 0, v_url_7_);
lean_ctor_set(v___x_18_, 1, v___x_14_);
lean_ctor_set(v___x_18_, 2, v___x_9_);
v___x_19_ = l_String_Slice_Pos_prevn(v___x_18_, v___x_9_, v___x_10_);
lean_dec_ref_known(v___x_18_, 3);
v___x_20_ = lean_string_utf8_extract_fast(v_url_7_, v___x_14_, v___x_19_);
lean_dec(v___x_19_);
lean_dec_ref(v_url_7_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_30_ = lean_string_utf8_byte_size(v_rev_29_);
v___x_31_ = lean_unsigned_to_nat(40u);
v___x_32_ = lean_nat_dec_eq(v___x_30_, v___x_31_);
if (v___x_32_ == 0)
{
return v___x_32_;
}
else
{
uint8_t v___x_33_; 
v___x_33_ = l_Lake_isHex(v_rev_29_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Lake_Git_isFullObjectName(v_rev_34_);
lean_dec_ref(v_rev_34_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object* v_rev_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_42_ = lean_string_utf8_byte_size(v_rev_41_);
v___x_43_ = lean_unsigned_to_nat(40u);
v___x_44_ = lean_nat_dec_eq(v___x_42_, v___x_43_);
if (v___x_44_ == 0)
{
return v___x_44_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = l_Lake_isHex(v_rev_41_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object* v_rev_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Lake_GitRev_isFullSha1(v_rev_46_);
lean_dec_ref(v_rev_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object* v_remote_50_, lean_object* v_rev_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_53_ = lean_string_append(v_remote_50_, v___x_52_);
v___x_54_ = lean_string_append(v___x_53_, v_rev_51_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object* v_remote_55_, lean_object* v_rev_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lake_GitRev_withRemote(v_remote_55_, v_rev_56_);
lean_dec_ref(v_rev_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object* v_x_58_){
_start:
{
lean_inc_ref(v_x_58_);
return v_x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lake_GitRepo_instCoeFilePath___lam__0(v_x_59_);
lean_dec_ref(v_x_59_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_66_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = l_System_FilePath_isDir(v_repo_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_69_, lean_object* v_a_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lake_GitRepo_dirExists(v_repo_69_);
lean_dec_ref(v_repo_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_gitExists(lean_object* v_repo_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_76_ = l_System_FilePath_join(v_repo_73_, v___x_75_);
v___x_77_ = l_System_FilePath_pathExists(v___x_76_);
lean_dec_ref(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gitExists___boxed(lean_object* v_repo_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lake_GitRepo_gitExists(v_repo_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_86_, lean_object* v_repo_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_90_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_91_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v_repo_87_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_95_ = 1;
v___x_96_ = 0;
v___x_97_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_97_, 0, v___x_90_);
lean_ctor_set(v___x_97_, 1, v___x_91_);
lean_ctor_set(v___x_97_, 2, v_args_86_);
lean_ctor_set(v___x_97_, 3, v___x_92_);
lean_ctor_set(v___x_97_, 4, v___x_94_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*5, v___x_95_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*5 + 1, v___x_96_);
v___x_98_ = l_Lake_captureProc_x27(v___x_97_, v_a_88_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_115_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_a_100_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_115_ == 0)
{
v___x_102_ = v___x_98_;
v_isShared_103_ = v_isSharedCheck_115_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_115_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_stdout_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_str_108_; lean_object* v_startInclusive_109_; lean_object* v_endExclusive_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v_stdout_104_ = lean_ctor_get(v_a_99_, 0);
lean_inc_ref(v_stdout_104_);
lean_dec(v_a_99_);
v___x_105_ = lean_string_utf8_byte_size(v_stdout_104_);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v_stdout_104_);
lean_ctor_set(v___x_106_, 1, v___x_93_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
v___x_107_ = l_String_Slice_trimAscii(v___x_106_);
v_str_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_str_108_);
v_startInclusive_109_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_startInclusive_109_);
v_endExclusive_110_ = lean_ctor_get(v___x_107_, 2);
lean_inc(v_endExclusive_110_);
lean_dec_ref(v___x_107_);
v___x_111_ = lean_string_utf8_extract_fast(v_str_108_, v_startInclusive_109_, v_endExclusive_110_);
lean_dec(v_endExclusive_110_);
lean_dec(v_startInclusive_109_);
lean_dec_ref(v_str_108_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_111_);
v___x_113_ = v___x_102_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_a_100_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
else
{
lean_object* v_a_116_; lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_116_ = lean_ctor_get(v___x_98_, 0);
v_a_117_ = lean_ctor_get(v___x_98_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_98_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_inc(v_a_116_);
lean_dec(v___x_98_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_116_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_125_, lean_object* v_repo_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lake_GitRepo_captureGit(v_args_125_, v_repo_126_, v_a_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_130_, lean_object* v_repo_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_133_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_134_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v_repo_131_);
v___x_136_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_137_ = 1;
v___x_138_ = 0;
v___x_139_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_139_, 0, v___x_133_);
lean_ctor_set(v___x_139_, 1, v___x_134_);
lean_ctor_set(v___x_139_, 2, v_args_130_);
lean_ctor_set(v___x_139_, 3, v___x_135_);
lean_ctor_set(v___x_139_, 4, v___x_136_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*5, v___x_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*5 + 1, v___x_138_);
v___x_140_ = l_Lake_captureProc_x3f(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_141_, lean_object* v_repo_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lake_GitRepo_captureGit_x3f(v_args_141_, v_repo_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_145_, lean_object* v_repo_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_149_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_150_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v_repo_146_);
v___x_152_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_153_ = 1;
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_155_, 0, v___x_149_);
lean_ctor_set(v___x_155_, 1, v___x_150_);
lean_ctor_set(v___x_155_, 2, v_args_145_);
lean_ctor_set(v___x_155_, 3, v___x_151_);
lean_ctor_set(v___x_155_, 4, v___x_152_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*5, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*5 + 1, v___x_154_);
v___x_156_ = lean_box(0);
v___x_157_ = l_Lake_proc(v___x_155_, v___x_153_, v___x_156_, v_a_147_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_158_, lean_object* v_repo_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_GitRepo_execGit(v_args_158_, v_repo_159_, v_a_160_);
return v_res_162_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_163_, lean_object* v_repo_164_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_166_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_167_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v_repo_164_);
v___x_169_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_170_ = 1;
v___x_171_ = 0;
v___x_172_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_172_, 0, v___x_166_);
lean_ctor_set(v___x_172_, 1, v___x_167_);
lean_ctor_set(v___x_172_, 2, v_args_163_);
lean_ctor_set(v___x_172_, 3, v___x_168_);
lean_ctor_set(v___x_172_, 4, v___x_169_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*5, v___x_170_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*5 + 1, v___x_171_);
v___x_173_ = l_Lake_testProc(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_174_, lean_object* v_repo_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lake_GitRepo_testGit(v_args_174_, v_repo_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(uint8_t v___x_179_, uint8_t v___x_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
if (v___x_179_ == 0)
{
uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_184_ = 1;
v___x_185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_185_, 0, v___y_181_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_array_push(v___y_182_, v___x_185_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_189_, 0, v___y_181_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_180_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_array_push(v___y_182_, v___x_189_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed(lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
uint8_t v___x_1996__boxed_198_; uint8_t v___x_1997__boxed_199_; lean_object* v_res_200_; 
v___x_1996__boxed_198_ = lean_unbox(v___x_193_);
v___x_1997__boxed_199_ = lean_unbox(v___x_194_);
v_res_200_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_1996__boxed_198_, v___x_1997__boxed_199_, v___y_195_, v___y_196_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(lean_object* v_stderr_202_, lean_object* v___x_203_, lean_object* v___y_204_, lean_object* v_____r_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_string_utf8_byte_size(v_stderr_202_);
v___x_209_ = lean_nat_dec_eq(v___x_208_, v___x_203_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0));
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v_stderr_202_);
lean_ctor_set(v___x_211_, 1, v___x_203_);
lean_ctor_set(v___x_211_, 2, v___x_208_);
v___x_212_ = l_String_Slice_trimAscii(v___x_211_);
v___x_213_ = l_String_Slice_toString(v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = lean_string_append(v___x_210_, v___x_213_);
lean_dec_ref(v___x_213_);
v___x_215_ = lean_apply_3(v___y_204_, v___x_214_, v___y_206_, lean_box(0));
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec_ref(v___y_204_);
lean_dec(v___x_203_);
lean_dec_ref(v_stderr_202_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___y_206_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___boxed(lean_object* v_stderr_218_, lean_object* v___x_219_, lean_object* v___y_220_, lean_object* v_____r_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_218_, v___x_219_, v___y_220_, v_____r_221_, v___y_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(lean_object* v_args_227_, lean_object* v_repo_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_a_232_; lean_object* v_a_233_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_235_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_236_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_repo_228_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_240_ = 1;
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_242_, 0, v___x_235_);
lean_ctor_set(v___x_242_, 1, v___x_236_);
lean_ctor_set(v___x_242_, 2, v_args_227_);
lean_ctor_set(v___x_242_, 3, v___x_237_);
lean_ctor_set(v___x_242_, 4, v___x_239_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*5, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*5 + 1, v___x_241_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_array_get_size(v_a_229_);
lean_inc_ref(v___x_242_);
v___x_245_ = l_Lake_mkCmdLog(v___x_242_);
v___x_246_ = 0;
v___x_247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*1, v___x_246_);
v___x_248_ = lean_array_push(v_a_229_, v___x_247_);
v___x_249_ = l_IO_Process_output(v___x_242_, v___x_243_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; uint32_t v_exitCode_251_; lean_object* v_stdout_252_; lean_object* v_stderr_253_; uint32_t v___x_254_; uint8_t v___x_255_; lean_object* v___y_257_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___y_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref_known(v___x_249_, 1);
v_exitCode_251_ = lean_ctor_get_uint32(v_a_250_, sizeof(void*)*2);
v_stdout_252_ = lean_ctor_get(v_a_250_, 0);
lean_inc_ref(v_stdout_252_);
v_stderr_253_ = lean_ctor_get(v_a_250_, 1);
lean_inc_ref(v_stderr_253_);
lean_dec(v_a_250_);
v___x_254_ = 0;
v___x_255_ = lean_uint32_dec_eq(v_exitCode_251_, v___x_254_);
v___x_270_ = lean_box(v___x_255_);
v___x_271_ = lean_box(v___x_246_);
v___y_272_ = lean_alloc_closure((void*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed), 5, 2);
lean_closure_set(v___y_272_, 0, v___x_270_);
lean_closure_set(v___y_272_, 1, v___x_271_);
v___x_273_ = lean_string_utf8_byte_size(v_stdout_252_);
v___x_274_ = lean_nat_dec_eq(v___x_273_, v___x_238_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v_a_282_; lean_object* v___x_283_; 
v___x_275_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0));
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v_stdout_252_);
lean_ctor_set(v___x_276_, 1, v___x_238_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
v___x_277_ = l_String_Slice_trimAscii(v___x_276_);
v___x_278_ = l_String_Slice_toString(v___x_277_);
lean_dec_ref(v___x_277_);
v___x_279_ = lean_string_append(v___x_275_, v___x_278_);
lean_dec_ref(v___x_278_);
v___x_280_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_255_, v___x_246_, v___x_279_, v___x_248_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
v_a_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_a_282_);
lean_dec_ref(v___x_280_);
v___x_283_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_253_, v___x_238_, v___y_272_, v_a_281_, v_a_282_);
v___y_257_ = v___x_283_;
goto v___jp_256_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec_ref(v_stdout_252_);
v___x_284_ = lean_box(0);
v___x_285_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_253_, v___x_238_, v___y_272_, v___x_284_, v___x_248_);
v___y_257_ = v___x_285_;
goto v___jp_256_;
}
v___jp_256_:
{
if (lean_obj_tag(v___y_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_a_258_ = lean_ctor_get(v___y_257_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v___y_257_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___y_257_, 0);
lean_dec(v_unused_267_);
v___x_260_ = v___y_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___y_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_box(v___x_255_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_a_258_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_a_268_; lean_object* v_a_269_; 
v_a_268_ = lean_ctor_get(v___y_257_, 0);
lean_inc(v_a_268_);
v_a_269_ = lean_ctor_get(v___y_257_, 1);
lean_inc(v_a_269_);
lean_dec_ref_known(v___y_257_, 2);
v_a_232_ = v_a_268_;
v_a_233_ = v_a_269_;
goto v___jp_231_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_a_286_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_249_, 1);
v___x_287_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1));
v___x_288_ = lean_io_error_to_string(v_a_286_);
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = 3;
v___x_291_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___x_290_);
v___x_292_ = lean_array_push(v___x_248_, v___x_291_);
v___x_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_244_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
return v___x_293_;
}
v___jp_231_:
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_234_, 0, v_a_232_);
lean_ctor_set(v___x_234_, 1, v_a_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___boxed(lean_object* v_args_294_, lean_object* v_repo_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(v_args_294_, v_repo_295_, v_a_296_);
return v_res_298_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_301_ = lean_unsigned_to_nat(3u);
v___x_302_ = lean_mk_empty_array_with_capacity(v___x_301_);
v___x_303_ = lean_array_push(v___x_302_, v___x_300_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_304_, lean_object* v_repo_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_308_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_309_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_310_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_311_ = lean_array_push(v___x_310_, v_url_304_);
v___x_312_ = lean_array_push(v___x_311_, v_repo_305_);
v___x_313_ = lean_box(0);
v___x_314_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_315_ = 1;
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_317_, 0, v___x_308_);
lean_ctor_set(v___x_317_, 1, v___x_309_);
lean_ctor_set(v___x_317_, 2, v___x_312_);
lean_ctor_set(v___x_317_, 3, v___x_313_);
lean_ctor_set(v___x_317_, 4, v___x_314_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*5, v___x_315_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*5 + 1, v___x_316_);
v___x_318_ = l_Lake_proc(v___x_317_, v___x_315_, v___x_313_, v_a_306_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_319_, lean_object* v_repo_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lake_GitRepo_clone(v_url_319_, v_repo_320_, v_a_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_335_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_336_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_337_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_repo_332_);
v___x_339_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_340_ = 1;
v___x_341_ = 0;
v___x_342_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_342_, 0, v___x_336_);
lean_ctor_set(v___x_342_, 1, v___x_337_);
lean_ctor_set(v___x_342_, 2, v___x_335_);
lean_ctor_set(v___x_342_, 3, v___x_338_);
lean_ctor_set(v___x_342_, 4, v___x_339_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*5, v___x_340_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*5 + 1, v___x_341_);
v___x_343_ = lean_box(0);
v___x_344_ = l_Lake_proc(v___x_342_, v___x_340_, v___x_343_, v_a_333_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lake_GitRepo_quietInit(v_repo_345_, v_a_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object* v_repo_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_361_ = ((lean_object*)(l_Lake_GitRepo_bareInit___closed__1));
v___x_362_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_363_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_repo_358_);
v___x_365_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_366_ = 1;
v___x_367_ = 0;
v___x_368_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_368_, 0, v___x_362_);
lean_ctor_set(v___x_368_, 1, v___x_363_);
lean_ctor_set(v___x_368_, 2, v___x_361_);
lean_ctor_set(v___x_368_, 3, v___x_364_);
lean_ctor_set(v___x_368_, 4, v___x_365_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*5, v___x_366_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*5 + 1, v___x_367_);
v___x_369_ = lean_box(0);
v___x_370_ = l_Lake_proc(v___x_368_, v___x_366_, v___x_369_, v_a_359_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object* v_repo_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lake_GitRepo_bareInit(v_repo_371_, v_a_372_);
return v_res_374_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_383_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_385_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_386_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_387_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_388_, 0, v_repo_383_);
v___x_389_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_390_ = 1;
v___x_391_ = 0;
v___x_392_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_392_, 0, v___x_386_);
lean_ctor_set(v___x_392_, 1, v___x_387_);
lean_ctor_set(v___x_392_, 2, v___x_385_);
lean_ctor_set(v___x_392_, 3, v___x_388_);
lean_ctor_set(v___x_392_, 4, v___x_389_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5, v___x_390_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5 + 1, v___x_391_);
v___x_393_ = l_Lake_testProc(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_394_, lean_object* v_a_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Lake_GitRepo_insideWorkTree(v_repo_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_402_ = lean_unsigned_to_nat(4u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_array_push(v___x_403_, v___x_401_);
return v___x_404_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_406_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_407_ = lean_array_push(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_409_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_410_ = lean_array_push(v___x_409_, v___x_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_411_, lean_object* v_remote_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_415_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_416_ = lean_array_push(v___x_415_, v_remote_412_);
v___x_417_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_418_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_repo_411_);
v___x_420_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_421_ = 1;
v___x_422_ = 0;
v___x_423_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_423_, 0, v___x_417_);
lean_ctor_set(v___x_423_, 1, v___x_418_);
lean_ctor_set(v___x_423_, 2, v___x_416_);
lean_ctor_set(v___x_423_, 3, v___x_419_);
lean_ctor_set(v___x_423_, 4, v___x_420_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5, v___x_421_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*5 + 1, v___x_422_);
v___x_424_ = lean_box(0);
v___x_425_ = l_Lake_proc(v___x_423_, v___x_421_, v___x_424_, v_a_413_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_426_, lean_object* v_remote_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lake_GitRepo_fetch(v_repo_426_, v_remote_427_, v_a_428_);
return v_res_430_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__0));
v___x_435_ = lean_unsigned_to_nat(5u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_435_);
v___x_437_ = lean_array_push(v___x_436_, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__4(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_439_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__3, &l_Lake_GitRepo_addWorktreeDetach___closed__3_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__3);
v___x_440_ = lean_array_push(v___x_439_, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__5(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_442_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__4, &l_Lake_GitRepo_addWorktreeDetach___closed__4_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__4);
v___x_443_ = lean_array_push(v___x_442_, v___x_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object* v_path_444_, lean_object* v_rev_445_, lean_object* v_repo_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_449_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__5, &l_Lake_GitRepo_addWorktreeDetach___closed__5_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__5);
v___x_450_ = lean_array_push(v___x_449_, v_path_444_);
v___x_451_ = lean_array_push(v___x_450_, v_rev_445_);
v___x_452_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_453_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_repo_446_);
v___x_455_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_456_ = 1;
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_458_, 0, v___x_452_);
lean_ctor_set(v___x_458_, 1, v___x_453_);
lean_ctor_set(v___x_458_, 2, v___x_451_);
lean_ctor_set(v___x_458_, 3, v___x_454_);
lean_ctor_set(v___x_458_, 4, v___x_455_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*5, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*5 + 1, v___x_457_);
v___x_459_ = lean_box(0);
v___x_460_ = l_Lake_proc(v___x_458_, v___x_456_, v___x_459_, v_a_447_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object* v_path_461_, lean_object* v_rev_462_, lean_object* v_repo_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lake_GitRepo_addWorktreeDetach(v_path_461_, v_rev_462_, v_repo_463_, v_a_464_);
return v_res_466_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_469_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_470_ = lean_unsigned_to_nat(3u);
v___x_471_ = lean_mk_empty_array_with_capacity(v___x_470_);
v___x_472_ = lean_array_push(v___x_471_, v___x_469_);
return v___x_472_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_474_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_475_ = lean_array_push(v___x_474_, v___x_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_476_, lean_object* v_repo_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_480_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_481_ = lean_array_push(v___x_480_, v_branch_476_);
v___x_482_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_483_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_repo_477_);
v___x_485_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_486_ = 1;
v___x_487_ = 0;
v___x_488_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_488_, 0, v___x_482_);
lean_ctor_set(v___x_488_, 1, v___x_483_);
lean_ctor_set(v___x_488_, 2, v___x_481_);
lean_ctor_set(v___x_488_, 3, v___x_484_);
lean_ctor_set(v___x_488_, 4, v___x_485_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5, v___x_486_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*5 + 1, v___x_487_);
v___x_489_ = lean_box(0);
v___x_490_ = l_Lake_proc(v___x_488_, v___x_486_, v___x_489_, v_a_478_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_491_, lean_object* v_repo_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lake_GitRepo_checkoutBranch(v_branch_491_, v_repo_492_, v_a_493_);
return v_res_495_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_498_ = lean_unsigned_to_nat(4u);
v___x_499_ = lean_mk_empty_array_with_capacity(v___x_498_);
v___x_500_ = lean_array_push(v___x_499_, v___x_497_);
return v___x_500_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_502_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__1, &l_Lake_GitRepo_checkoutDetach___closed__1_once, _init_l_Lake_GitRepo_checkoutDetach___closed__1);
v___x_503_ = lean_array_push(v___x_502_, v___x_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_504_, lean_object* v_repo_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_508_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_509_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_510_ = lean_array_push(v___x_509_, v_hash_504_);
v___x_511_ = lean_array_push(v___x_510_, v___x_508_);
v___x_512_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_513_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_repo_505_);
v___x_515_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_516_ = 1;
v___x_517_ = 0;
v___x_518_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_518_, 0, v___x_512_);
lean_ctor_set(v___x_518_, 1, v___x_513_);
lean_ctor_set(v___x_518_, 2, v___x_511_);
lean_ctor_set(v___x_518_, 3, v___x_514_);
lean_ctor_set(v___x_518_, 4, v___x_515_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*5, v___x_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*5 + 1, v___x_517_);
v___x_519_ = lean_box(0);
v___x_520_ = l_Lake_proc(v___x_518_, v___x_516_, v___x_519_, v_a_506_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_521_, lean_object* v_repo_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_GitRepo_checkoutDetach(v_hash_521_, v_repo_522_, v_a_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto(lean_object* v_repo_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_537_ = ((lean_object*)(l_Lake_GitRepo_gcAuto___closed__2));
v___x_538_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_539_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v_repo_534_);
v___x_541_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_542_ = 1;
v___x_543_ = 0;
v___x_544_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_544_, 0, v___x_538_);
lean_ctor_set(v___x_544_, 1, v___x_539_);
lean_ctor_set(v___x_544_, 2, v___x_537_);
lean_ctor_set(v___x_544_, 3, v___x_540_);
lean_ctor_set(v___x_544_, 4, v___x_541_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*5, v___x_542_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*5 + 1, v___x_543_);
v___x_545_ = lean_box(0);
v___x_546_ = l_Lake_proc(v___x_544_, v___x_542_, v___x_545_, v_a_535_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto___boxed(lean_object* v_repo_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lake_GitRepo_gcAuto(v_repo_547_, v_a_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_562_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_563_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_564_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v_repo_559_);
v___x_566_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_567_ = 1;
v___x_568_ = 0;
v___x_569_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_569_, 0, v___x_563_);
lean_ctor_set(v___x_569_, 1, v___x_564_);
lean_ctor_set(v___x_569_, 2, v___x_562_);
lean_ctor_set(v___x_569_, 3, v___x_565_);
lean_ctor_set(v___x_569_, 4, v___x_566_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*5, v___x_567_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*5 + 1, v___x_568_);
v___x_570_ = lean_box(0);
v___x_571_ = l_Lake_proc(v___x_569_, v___x_567_, v___x_570_, v_a_560_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lake_GitRepo_clean(v_repo_572_, v_a_573_);
return v_res_575_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_579_ = lean_unsigned_to_nat(4u);
v___x_580_ = lean_mk_empty_array_with_capacity(v___x_579_);
v___x_581_ = lean_array_push(v___x_580_, v___x_578_);
return v___x_581_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_583_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_584_ = lean_array_push(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_586_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_587_ = lean_array_push(v___x_586_, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_588_, lean_object* v_repo_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_591_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_592_ = lean_array_push(v___x_591_, v_rev_588_);
v___x_593_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_594_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_repo_589_);
v___x_596_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_597_ = 1;
v___x_598_ = 0;
v___x_599_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_599_, 0, v___x_593_);
lean_ctor_set(v___x_599_, 1, v___x_594_);
lean_ctor_set(v___x_599_, 2, v___x_592_);
lean_ctor_set(v___x_599_, 3, v___x_595_);
lean_ctor_set(v___x_599_, 4, v___x_596_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*5, v___x_597_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*5 + 1, v___x_598_);
v___x_600_ = l_Lake_captureProc_x3f(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_601_, lean_object* v_repo_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_601_, v_repo_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object* v_rev_606_, lean_object* v_repo_607_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_609_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_610_ = lean_string_append(v_rev_606_, v___x_609_);
v___x_611_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_612_ = lean_array_push(v___x_611_, v___x_610_);
v___x_613_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_614_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v_repo_607_);
v___x_616_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_617_ = 1;
v___x_618_ = 0;
v___x_619_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_619_, 0, v___x_613_);
lean_ctor_set(v___x_619_, 1, v___x_614_);
lean_ctor_set(v___x_619_, 2, v___x_612_);
lean_ctor_set(v___x_619_, 3, v___x_615_);
lean_ctor_set(v___x_619_, 4, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*5, v___x_617_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*5 + 1, v___x_618_);
v___x_620_ = l_Lake_captureProc_x3f(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object* v_rev_621_, lean_object* v_repo_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lake_GitRepo_findCommit_x3f(v_rev_621_, v_repo_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_627_, lean_object* v_repo_628_, lean_object* v_a_629_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Lake_GitRev_isFullSha1(v_rev_627_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
lean_inc_ref(v_repo_628_);
lean_inc_ref(v_rev_627_);
v___x_632_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_627_, v_repo_628_);
if (lean_obj_tag(v___x_632_) == 1)
{
lean_object* v_val_633_; lean_object* v___x_634_; 
lean_dec_ref(v_repo_628_);
lean_dec_ref(v_rev_627_);
v_val_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_val_633_);
lean_ctor_set(v___x_634_, 1, v_a_629_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v___x_632_);
v___x_635_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_636_ = lean_string_append(v_repo_628_, v___x_635_);
v___x_637_ = lean_string_append(v___x_636_, v_rev_627_);
lean_dec_ref(v_rev_627_);
v___x_638_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___x_640_ = 3;
v___x_641_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_640_);
v___x_642_ = lean_array_get_size(v_a_629_);
v___x_643_ = lean_array_push(v_a_629_, v___x_641_);
v___x_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
return v___x_644_;
}
}
else
{
lean_object* v___x_645_; 
lean_dec_ref(v_repo_628_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_rev_627_);
lean_ctor_set(v___x_645_, 1, v_a_629_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_646_, lean_object* v_repo_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lake_GitRepo_resolveRevision(v_rev_646_, v_repo_647_, v_a_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_651_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
v___x_654_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_653_, v_repo_651_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
lean_inc_ref(v_repo_659_);
v___x_663_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_662_, v_repo_659_);
if (lean_obj_tag(v___x_663_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_665_; 
lean_dec_ref(v_repo_659_);
v_val_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_val_664_);
lean_ctor_set(v___x_665_, 1, v_a_660_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v___x_663_);
v___x_666_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_667_ = lean_string_append(v_repo_659_, v___x_666_);
v___x_668_ = 3;
v___x_669_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_668_);
v___x_670_ = lean_array_get_size(v_a_660_);
v___x_671_ = lean_array_push(v_a_660_, v___x_669_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lake_GitRepo_getHeadRevision(v_repo_673_, v_a_674_);
return v_res_676_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_679_ = lean_unsigned_to_nat(6u);
v___x_680_ = lean_mk_empty_array_with_capacity(v___x_679_);
v___x_681_ = lean_array_push(v___x_680_, v___x_678_);
return v___x_681_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_683_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__1, &l_Lake_GitRepo_fetchRevision_x3f___closed__1_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__1);
v___x_684_ = lean_array_push(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_686_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__2, &l_Lake_GitRepo_fetchRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2);
v___x_687_ = lean_array_push(v___x_686_, v___x_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__0));
v___x_689_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__3, &l_Lake_GitRepo_fetchRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3);
v___x_690_ = lean_array_push(v___x_689_, v___x_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object* v_repo_692_, lean_object* v_remote_693_, lean_object* v_rev_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_a_698_; lean_object* v_a_699_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_args_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_701_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__4, &l_Lake_GitRepo_fetchRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4);
v___x_702_ = lean_array_push(v___x_701_, v_remote_693_);
v_args_703_ = lean_array_push(v___x_702_, v_rev_694_);
v___x_704_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_705_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
lean_inc_ref(v_repo_692_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_repo_692_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_709_ = 1;
v___x_710_ = 0;
v___x_711_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_711_, 0, v___x_704_);
lean_ctor_set(v___x_711_, 1, v___x_705_);
lean_ctor_set(v___x_711_, 2, v_args_703_);
lean_ctor_set(v___x_711_, 3, v___x_706_);
lean_ctor_set(v___x_711_, 4, v___x_708_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5, v___x_709_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*5 + 1, v___x_710_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_array_get_size(v_a_695_);
lean_inc_ref(v___x_711_);
v___x_714_ = l_Lake_mkCmdLog(v___x_711_);
v___x_715_ = 0;
v___x_716_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*1, v___x_715_);
v___x_717_ = lean_array_push(v_a_695_, v___x_716_);
v___x_718_ = l_IO_Process_output(v___x_711_, v___x_712_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; uint32_t v_exitCode_720_; lean_object* v_stdout_721_; lean_object* v_stderr_722_; uint32_t v___x_723_; uint8_t v___x_724_; lean_object* v___y_726_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___y_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v_exitCode_720_ = lean_ctor_get_uint32(v_a_719_, sizeof(void*)*2);
v_stdout_721_ = lean_ctor_get(v_a_719_, 0);
lean_inc_ref(v_stdout_721_);
v_stderr_722_ = lean_ctor_get(v_a_719_, 1);
lean_inc_ref(v_stderr_722_);
lean_dec(v_a_719_);
v___x_723_ = 0;
v___x_724_ = lean_uint32_dec_eq(v_exitCode_720_, v___x_723_);
v___x_758_ = lean_box(v___x_724_);
v___x_759_ = lean_box(v___x_715_);
v___y_760_ = lean_alloc_closure((void*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed), 5, 2);
lean_closure_set(v___y_760_, 0, v___x_758_);
lean_closure_set(v___y_760_, 1, v___x_759_);
v___x_761_ = lean_string_utf8_byte_size(v_stdout_721_);
v___x_762_ = lean_nat_dec_eq(v___x_761_, v___x_707_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_a_769_; lean_object* v_a_770_; lean_object* v___x_771_; 
v___x_763_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0));
v___x_764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_764_, 0, v_stdout_721_);
lean_ctor_set(v___x_764_, 1, v___x_707_);
lean_ctor_set(v___x_764_, 2, v___x_761_);
v___x_765_ = l_String_Slice_trimAscii(v___x_764_);
v___x_766_ = l_String_Slice_toString(v___x_765_);
lean_dec_ref(v___x_765_);
v___x_767_ = lean_string_append(v___x_763_, v___x_766_);
lean_dec_ref(v___x_766_);
v___x_768_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_724_, v___x_715_, v___x_767_, v___x_717_);
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
v_a_770_ = lean_ctor_get(v___x_768_, 1);
lean_inc(v_a_770_);
lean_dec_ref(v___x_768_);
v___x_771_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_722_, v___x_707_, v___y_760_, v_a_769_, v_a_770_);
v___y_726_ = v___x_771_;
goto v___jp_725_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_stdout_721_);
v___x_772_ = lean_box(0);
v___x_773_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_722_, v___x_707_, v___y_760_, v___x_772_, v___x_717_);
v___y_726_ = v___x_773_;
goto v___jp_725_;
}
v___jp_725_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
if (v___x_724_ == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_repo_692_);
v_a_727_ = lean_ctor_get(v___y_726_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v___y_726_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___y_726_, 0);
lean_dec(v_unused_735_);
v___x_729_ = v___y_726_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___y_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_712_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_754_; 
v_a_736_ = lean_ctor_get(v___y_726_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___y_726_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___y_726_, 0);
lean_dec(v_unused_755_);
v___x_738_ = v___y_726_;
v_isShared_739_ = v_isSharedCheck_754_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___y_726_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_754_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lake_GitRev_fetchHead___closed__0));
lean_inc_ref(v_repo_692_);
v___x_741_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_740_, v_repo_692_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v___x_743_; 
lean_dec_ref(v_repo_692_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_a_736_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec(v___x_741_);
v___x_745_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__5));
v___x_746_ = lean_string_append(v_repo_692_, v___x_745_);
v___x_747_ = 3;
v___x_748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*1, v___x_747_);
v___x_749_ = lean_array_get_size(v_a_736_);
v___x_750_ = lean_array_push(v_a_736_, v___x_748_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 1);
lean_ctor_set(v___x_738_, 1, v___x_750_);
lean_ctor_set(v___x_738_, 0, v___x_749_);
v___x_752_ = v___x_738_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; 
lean_dec_ref(v_repo_692_);
v_a_756_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_a_756_);
v_a_757_ = lean_ctor_get(v___y_726_, 1);
lean_inc(v_a_757_);
lean_dec_ref_known(v___y_726_, 2);
v_a_698_ = v_a_756_;
v_a_699_ = v_a_757_;
goto v___jp_697_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec_ref(v_repo_692_);
v_a_774_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_718_, 1);
v___x_775_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1));
v___x_776_ = lean_io_error_to_string(v_a_774_);
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
lean_dec_ref(v___x_776_);
v___x_778_ = 3;
v___x_779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_778_);
v___x_780_ = lean_array_push(v___x_717_, v___x_779_);
v_a_698_ = v___x_713_;
v_a_699_ = v___x_780_;
goto v___jp_697_;
}
v___jp_697_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v_a_698_);
lean_ctor_set(v___x_700_, 1, v_a_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object* v_repo_781_, lean_object* v_remote_782_, lean_object* v_rev_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_781_, v_remote_782_, v_rev_783_, v_a_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg(){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___closed__0));
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg___boxed(lean_object* v___dummy_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
return v_res_792_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0(void){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___redArg();
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_796_);
lean_dec_ref(v_s_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_it_804_; lean_object* v_startInclusive_805_; lean_object* v_endExclusive_806_; 
if (lean_obj_tag(v_a_801_) == 0)
{
lean_object* v_currPos_811_; lean_object* v_searcher_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_835_; 
v_currPos_811_ = lean_ctor_get(v_a_801_, 0);
v_searcher_812_ = lean_ctor_get(v_a_801_, 1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_835_ == 0)
{
v___x_814_ = v_a_801_;
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_searcher_812_);
lean_inc(v_currPos_811_);
lean_dec(v_a_801_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v_decide_816_; 
v_decide_816_ = lean_nat_dec_eq(v_searcher_812_, v___x_800_);
if (v_decide_816_ == 0)
{
uint32_t v___x_817_; uint32_t v___x_818_; uint8_t v___x_819_; 
v___x_817_ = 10;
v___x_818_ = lean_string_utf8_get_fast(v___x_798_, v_searcher_812_);
v___x_819_ = lean_uint32_dec_eq(v___x_818_, v___x_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_string_utf8_next_fast(v___x_798_, v_searcher_812_);
lean_dec(v_searcher_812_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_820_);
v___x_822_ = v___x_814_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_currPos_811_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
v_a_801_ = v___x_822_;
goto _start;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_slice_828_; lean_object* v_nextIt_830_; 
v___x_825_ = lean_string_utf8_next_fast(v___x_798_, v_searcher_812_);
v___x_826_ = lean_nat_sub(v___x_825_, v_searcher_812_);
v___x_827_ = lean_nat_add(v_searcher_812_, v___x_826_);
lean_dec(v___x_826_);
v_slice_828_ = l_String_Slice_subslice_x21(v___x_799_, v_currPos_811_, v_searcher_812_);
lean_inc(v___x_827_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_827_);
lean_ctor_set(v___x_814_, 0, v___x_827_);
v_nextIt_830_ = v___x_814_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_827_);
v_nextIt_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v_startInclusive_831_; lean_object* v_endExclusive_832_; 
v_startInclusive_831_ = lean_ctor_get(v_slice_828_, 0);
lean_inc(v_startInclusive_831_);
v_endExclusive_832_ = lean_ctor_get(v_slice_828_, 1);
lean_inc(v_endExclusive_832_);
lean_dec_ref(v_slice_828_);
v_it_804_ = v_nextIt_830_;
v_startInclusive_805_ = v_startInclusive_831_;
v_endExclusive_806_ = v_endExclusive_832_;
goto v___jp_803_;
}
}
}
else
{
lean_object* v___x_834_; 
lean_del_object(v___x_814_);
lean_dec(v_searcher_812_);
v___x_834_ = lean_box(1);
lean_inc(v___x_800_);
v_it_804_ = v___x_834_;
v_startInclusive_805_ = v_currPos_811_;
v_endExclusive_806_ = v___x_800_;
goto v___jp_803_;
}
}
}
else
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_798_);
return v_b_802_;
}
v___jp_803_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc_ref(v___x_798_);
v___x_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_807_, 0, v___x_798_);
lean_ctor_set(v___x_807_, 1, v_startInclusive_805_);
lean_ctor_set(v___x_807_, 2, v_endExclusive_806_);
v___x_808_ = l_String_Slice_toString(v___x_807_);
lean_dec_ref_known(v___x_807_, 3);
v___x_809_ = lean_array_push(v_b_802_, v___x_808_);
v_a_801_ = v_it_804_;
v_b_802_ = v___x_809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v_a_839_, lean_object* v_b_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_836_, v___x_837_, v___x_838_, v_a_839_, v_b_840_);
lean_dec_ref(v___x_837_);
return v_res_841_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_850_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_851_ = lean_unsigned_to_nat(2u);
v___x_852_ = lean_mk_empty_array_with_capacity(v___x_851_);
v___x_853_ = lean_array_push(v___x_852_, v___x_850_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_854_, lean_object* v_n_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___y_859_; lean_object* v_args_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_args_905_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_dec_eq(v_n_855_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = l_Nat_reprFast(v_n_855_);
v___x_909_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_910_ = lean_array_push(v___x_909_, v___x_908_);
v___x_911_ = l_Array_append___redArg(v_args_905_, v___x_910_);
lean_dec_ref(v___x_910_);
v___y_859_ = v___x_911_;
goto v___jp_858_;
}
else
{
lean_dec(v_n_855_);
v___y_859_ = v_args_905_;
goto v___jp_858_;
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_860_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_861_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_862_, 0, v_repo_854_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_865_ = 1;
v___x_866_ = 0;
v___x_867_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_867_, 0, v___x_860_);
lean_ctor_set(v___x_867_, 1, v___x_861_);
lean_ctor_set(v___x_867_, 2, v___y_859_);
lean_ctor_set(v___x_867_, 3, v___x_862_);
lean_ctor_set(v___x_867_, 4, v___x_864_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*5, v___x_865_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*5 + 1, v___x_866_);
v___x_868_ = l_Lake_captureProc_x27(v___x_867_, v_a_856_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_895_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_a_870_ = lean_ctor_get(v___x_868_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_895_ == 0)
{
v___x_872_ = v___x_868_;
v_isShared_873_ = v_isSharedCheck_895_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_895_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_stdout_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_str_878_; lean_object* v_startInclusive_879_; lean_object* v_endExclusive_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_894_; 
v_stdout_874_ = lean_ctor_get(v_a_869_, 0);
lean_inc_ref(v_stdout_874_);
lean_dec(v_a_869_);
v___x_875_ = lean_string_utf8_byte_size(v_stdout_874_);
v___x_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_876_, 0, v_stdout_874_);
lean_ctor_set(v___x_876_, 1, v___x_863_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
v___x_877_ = l_String_Slice_trimAscii(v___x_876_);
v_str_878_ = lean_ctor_get(v___x_877_, 0);
v_startInclusive_879_ = lean_ctor_get(v___x_877_, 1);
v_endExclusive_880_ = lean_ctor_get(v___x_877_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_894_ == 0)
{
v___x_882_ = v___x_877_;
v_isShared_883_ = v_isSharedCheck_894_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_endExclusive_880_);
lean_inc(v_startInclusive_879_);
lean_inc(v_str_878_);
lean_dec(v___x_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_894_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_string_utf8_extract_fast(v_str_878_, v_startInclusive_879_, v_endExclusive_880_);
lean_dec(v_endExclusive_880_);
lean_dec(v_startInclusive_879_);
lean_dec_ref(v_str_878_);
v___x_885_ = lean_string_utf8_byte_size(v___x_884_);
lean_inc_ref(v___x_884_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 2, v___x_885_);
lean_ctor_set(v___x_882_, 1, v___x_863_);
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v___x_885_);
v___x_887_ = v_reuseFailAlloc_893_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_888_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0);
v___x_889_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_884_, v___x_887_, v___x_885_, v___x_888_, v___x_864_);
lean_dec_ref(v___x_887_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_889_);
v___x_891_ = v___x_872_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_a_870_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_896_ = lean_ctor_get(v___x_868_, 0);
v_a_897_ = lean_ctor_get(v___x_868_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_868_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_inc(v_a_896_);
lean_dec(v___x_868_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_896_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_912_, lean_object* v_n_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lake_GitRepo_getHeadRevisions(v_repo_912_, v_n_913_, v_a_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_917_, lean_object* v___x_918_, lean_object* v___x_919_, lean_object* v_inst_920_, lean_object* v_R_921_, lean_object* v_a_922_, lean_object* v_b_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_917_, v___x_918_, v___x_919_, v_a_922_, v_b_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_925_, lean_object* v___x_926_, lean_object* v___x_927_, lean_object* v_inst_928_, lean_object* v_R_929_, lean_object* v_a_930_, lean_object* v_b_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_925_, v___x_926_, v___x_927_, v_inst_928_, v_R_929_, v_a_930_, v_b_931_);
lean_dec_ref(v___x_926_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_933_, lean_object* v_remote_934_, lean_object* v_repo_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_rev_939_; lean_object* v___y_940_; uint8_t v___x_942_; 
v___x_942_ = l_Lake_GitRev_isFullSha1(v_rev_933_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_944_ = lean_string_append(v_remote_934_, v___x_943_);
v___x_945_ = lean_string_append(v___x_944_, v_rev_933_);
lean_inc_ref(v_repo_935_);
v___x_946_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_945_, v_repo_935_);
if (lean_obj_tag(v___x_946_) == 1)
{
lean_object* v_val_947_; 
lean_dec_ref(v_repo_935_);
lean_dec_ref(v_rev_933_);
v_val_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v___x_946_, 1);
v_rev_939_ = v_val_947_;
v___y_940_ = v_a_936_;
goto v___jp_938_;
}
else
{
lean_object* v___x_948_; 
lean_dec(v___x_946_);
lean_inc_ref(v_repo_935_);
lean_inc_ref(v_rev_933_);
v___x_948_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_933_, v_repo_935_);
if (lean_obj_tag(v___x_948_) == 1)
{
lean_object* v_val_949_; 
lean_dec_ref(v_repo_935_);
lean_dec_ref(v_rev_933_);
v_val_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_val_949_);
lean_dec_ref_known(v___x_948_, 1);
v_rev_939_ = v_val_949_;
v___y_940_ = v_a_936_;
goto v___jp_938_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v___x_948_);
v___x_950_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_951_ = lean_string_append(v_repo_935_, v___x_950_);
v___x_952_ = lean_string_append(v___x_951_, v_rev_933_);
lean_dec_ref(v_rev_933_);
v___x_953_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = 3;
v___x_956_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*1, v___x_955_);
v___x_957_ = lean_array_get_size(v_a_936_);
v___x_958_ = lean_array_push(v_a_936_, v___x_956_);
v___x_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
return v___x_959_;
}
}
}
else
{
lean_object* v___x_960_; 
lean_dec_ref(v_repo_935_);
lean_dec_ref(v_remote_934_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_rev_933_);
lean_ctor_set(v___x_960_, 1, v_a_936_);
return v___x_960_;
}
v___jp_938_:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_rev_939_);
lean_ctor_set(v___x_941_, 1, v___y_940_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_961_, lean_object* v_remote_962_, lean_object* v_repo_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_961_, v_remote_962_, v_repo_963_, v_a_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_967_, lean_object* v_rev_x3f_968_, lean_object* v_remote_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc_ref(v_remote_969_);
lean_inc_ref(v_repo_967_);
v___x_972_ = l_Lake_GitRepo_fetch(v_repo_967_, v_remote_969_, v_a_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
if (lean_obj_tag(v_rev_x3f_968_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 1);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 2);
v___x_974_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_975_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_974_, v_remote_969_, v_repo_967_, v_a_973_);
return v___x_975_;
}
else
{
lean_object* v_a_976_; lean_object* v_val_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_972_, 1);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_972_, 2);
v_val_977_ = lean_ctor_get(v_rev_x3f_968_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_rev_x3f_968_, 1);
v___x_978_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_977_, v_remote_969_, v_repo_967_, v_a_976_);
return v___x_978_;
}
}
else
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v_remote_969_);
lean_dec(v_rev_x3f_968_);
lean_dec_ref(v_repo_967_);
v_a_979_ = lean_ctor_get(v___x_972_, 0);
v_a_980_ = lean_ctor_get(v___x_972_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_972_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_inc(v_a_979_);
lean_dec(v___x_972_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_979_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_988_, lean_object* v_rev_x3f_989_, lean_object* v_remote_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lake_GitRepo_findRemoteRevision(v_repo_988_, v_rev_x3f_989_, v_remote_990_, v_a_991_);
return v_res_993_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_996_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_997_ = lean_unsigned_to_nat(3u);
v___x_998_ = lean_mk_empty_array_with_capacity(v___x_997_);
v___x_999_ = lean_array_push(v___x_998_, v___x_996_);
return v___x_999_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_1001_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_1002_ = lean_array_push(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_1003_, lean_object* v_repo_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1006_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_1007_ = lean_string_append(v___x_1006_, v_rev_1003_);
v___x_1008_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
v___x_1010_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1011_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_repo_1004_);
v___x_1013_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1014_ = 1;
v___x_1015_ = 0;
v___x_1016_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1016_, 0, v___x_1010_);
lean_ctor_set(v___x_1016_, 1, v___x_1011_);
lean_ctor_set(v___x_1016_, 2, v___x_1009_);
lean_ctor_set(v___x_1016_, 3, v___x_1012_);
lean_ctor_set(v___x_1016_, 4, v___x_1013_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*5, v___x_1014_);
lean_ctor_set_uint8(v___x_1016_, sizeof(void*)*5 + 1, v___x_1015_);
v___x_1017_ = l_Lake_testProc(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_1018_, lean_object* v_repo_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lake_GitRepo_branchExists(v_rev_1018_, v_repo_1019_);
lean_dec_ref(v_rev_1018_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__0(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1023_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_1024_ = lean_unsigned_to_nat(3u);
v___x_1025_ = lean_mk_empty_array_with_capacity(v___x_1024_);
v___x_1026_ = lean_array_push(v___x_1025_, v___x_1023_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_1028_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__0, &l_Lake_GitRepo_revisionExists___closed__0_once, _init_l_Lake_GitRepo_revisionExists___closed__0);
v___x_1029_ = lean_array_push(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_1030_, lean_object* v_repo_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1033_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_1034_ = lean_string_append(v_rev_1030_, v___x_1033_);
v___x_1035_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_1036_ = lean_array_push(v___x_1035_, v___x_1034_);
v___x_1037_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1038_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_repo_1031_);
v___x_1040_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1041_ = 1;
v___x_1042_ = 0;
v___x_1043_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1043_, 0, v___x_1037_);
lean_ctor_set(v___x_1043_, 1, v___x_1038_);
lean_ctor_set(v___x_1043_, 2, v___x_1036_);
lean_ctor_set(v___x_1043_, 3, v___x_1039_);
lean_ctor_set(v___x_1043_, 4, v___x_1040_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*5, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*5 + 1, v___x_1042_);
v___x_1044_ = l_Lake_testProc(v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_1045_, lean_object* v_repo_1046_, lean_object* v_a_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Lake_GitRepo_revisionExists(v_rev_1045_, v_repo_1046_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_1059_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1060_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_repo_1055_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1064_ = 1;
v___x_1065_ = 0;
v___x_1066_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1066_, 0, v___x_1059_);
lean_ctor_set(v___x_1066_, 1, v___x_1060_);
lean_ctor_set(v___x_1066_, 2, v___x_1058_);
lean_ctor_set(v___x_1066_, 3, v___x_1061_);
lean_ctor_set(v___x_1066_, 4, v___x_1063_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*5, v___x_1064_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*5 + 1, v___x_1065_);
v___x_1067_ = l_Lake_captureProc_x3f(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_val_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_n(v_val_1068_, 2);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = lean_string_utf8_byte_size(v_val_1068_);
v___x_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1070_, 0, v_val_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1062_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0);
v___x_1072_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_1068_, v___x_1070_, v___x_1069_, v___x_1071_, v___x_1063_);
lean_dec_ref_known(v___x_1070_, 3);
v___x_1073_ = lean_array_to_list(v___x_1072_);
return v___x_1073_;
}
else
{
lean_dec(v___x_1067_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lake_GitRepo_getTags(v_repo_1074_);
return v_res_1076_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_1080_ = lean_unsigned_to_nat(4u);
v___x_1081_ = lean_mk_empty_array_with_capacity(v___x_1080_);
v___x_1082_ = lean_array_push(v___x_1081_, v___x_1079_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_1084_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_1085_ = lean_array_push(v___x_1084_, v___x_1083_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_1087_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_1088_ = lean_array_push(v___x_1087_, v___x_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_1089_, lean_object* v_repo_1090_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1092_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_1093_ = lean_array_push(v___x_1092_, v_rev_1089_);
v___x_1094_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1095_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_repo_1090_);
v___x_1097_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1098_ = 1;
v___x_1099_ = 0;
v___x_1100_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1100_, 0, v___x_1094_);
lean_ctor_set(v___x_1100_, 1, v___x_1095_);
lean_ctor_set(v___x_1100_, 2, v___x_1093_);
lean_ctor_set(v___x_1100_, 3, v___x_1096_);
lean_ctor_set(v___x_1100_, 4, v___x_1097_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*5, v___x_1098_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*5 + 1, v___x_1099_);
v___x_1101_ = l_Lake_captureProc_x3f(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_1102_, lean_object* v_repo_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_GitRepo_findTag_x3f(v_rev_1102_, v_repo_1103_);
return v_res_1105_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_1109_ = lean_unsigned_to_nat(3u);
v___x_1110_ = lean_mk_empty_array_with_capacity(v___x_1109_);
v___x_1111_ = lean_array_push(v___x_1110_, v___x_1108_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_1113_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_1115_, lean_object* v_repo_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1118_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_1119_ = lean_array_push(v___x_1118_, v_remote_1115_);
v___x_1120_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1121_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_repo_1116_);
v___x_1123_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1124_ = 1;
v___x_1125_ = 0;
v___x_1126_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1126_, 0, v___x_1120_);
lean_ctor_set(v___x_1126_, 1, v___x_1121_);
lean_ctor_set(v___x_1126_, 2, v___x_1119_);
lean_ctor_set(v___x_1126_, 3, v___x_1122_);
lean_ctor_set(v___x_1126_, 4, v___x_1123_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*5, v___x_1124_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*5 + 1, v___x_1125_);
v___x_1127_ = l_Lake_captureProc_x3f(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_1128_, lean_object* v_repo_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1128_, v_repo_1129_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1132_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = lean_mk_empty_array_with_capacity(v___x_1133_);
v___x_1135_ = lean_array_push(v___x_1134_, v___x_1132_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__1(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_1137_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_1138_ = lean_array_push(v___x_1137_, v___x_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object* v_remote_1139_, lean_object* v_url_1140_, lean_object* v_repo_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1144_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__1, &l_Lake_GitRepo_addRemote___closed__1_once, _init_l_Lake_GitRepo_addRemote___closed__1);
v___x_1145_ = lean_array_push(v___x_1144_, v_remote_1139_);
v___x_1146_ = lean_array_push(v___x_1145_, v_url_1140_);
v___x_1147_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1148_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_repo_1141_);
v___x_1150_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1151_ = 1;
v___x_1152_ = 0;
v___x_1153_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1153_, 0, v___x_1147_);
lean_ctor_set(v___x_1153_, 1, v___x_1148_);
lean_ctor_set(v___x_1153_, 2, v___x_1146_);
lean_ctor_set(v___x_1153_, 3, v___x_1149_);
lean_ctor_set(v___x_1153_, 4, v___x_1150_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*5, v___x_1151_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*5 + 1, v___x_1152_);
v___x_1154_ = lean_box(0);
v___x_1155_ = l_Lake_proc(v___x_1153_, v___x_1151_, v___x_1154_, v_a_1142_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object* v_remote_1156_, lean_object* v_url_1157_, lean_object* v_repo_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lake_GitRepo_addRemote(v_remote_1156_, v_url_1157_, v_repo_1158_, v_a_1159_);
return v_res_1161_;
}
}
static lean_object* _init_l_Lake_GitRepo_setRemoteUrl___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = ((lean_object*)(l_Lake_GitRepo_setRemoteUrl___closed__0));
v___x_1164_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_1165_ = lean_array_push(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object* v_remote_1166_, lean_object* v_url_1167_, lean_object* v_repo_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1171_ = lean_obj_once(&l_Lake_GitRepo_setRemoteUrl___closed__1, &l_Lake_GitRepo_setRemoteUrl___closed__1_once, _init_l_Lake_GitRepo_setRemoteUrl___closed__1);
v___x_1172_ = lean_array_push(v___x_1171_, v_remote_1166_);
v___x_1173_ = lean_array_push(v___x_1172_, v_url_1167_);
v___x_1174_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1175_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_repo_1168_);
v___x_1177_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1178_ = 1;
v___x_1179_ = 0;
v___x_1180_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1180_, 0, v___x_1174_);
lean_ctor_set(v___x_1180_, 1, v___x_1175_);
lean_ctor_set(v___x_1180_, 2, v___x_1173_);
lean_ctor_set(v___x_1180_, 3, v___x_1176_);
lean_ctor_set(v___x_1180_, 4, v___x_1177_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*5, v___x_1178_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*5 + 1, v___x_1179_);
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lake_proc(v___x_1180_, v___x_1178_, v___x_1181_, v_a_1169_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object* v_remote_1183_, lean_object* v_url_1184_, lean_object* v_repo_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lake_GitRepo_setRemoteUrl(v_remote_1183_, v_url_1184_, v_repo_1185_, v_a_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_1189_, lean_object* v_repo_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1189_, v_repo_1190_);
if (lean_obj_tag(v___x_1192_) == 0)
{
return v___x_1192_;
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1194_; 
v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = l_Lake_Git_filterUrl_x3f(v_val_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_1195_, lean_object* v_repo_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_1195_, v_repo_1196_);
return v_res_1198_;
}
}
static lean_object* _init_l_Lake_GitRepo_pruneRemote___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = ((lean_object*)(l_Lake_GitRepo_pruneRemote___closed__0));
v___x_1201_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_1202_ = lean_array_push(v___x_1201_, v___x_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote(lean_object* v_remote_1203_, lean_object* v_repo_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1207_ = lean_obj_once(&l_Lake_GitRepo_pruneRemote___closed__1, &l_Lake_GitRepo_pruneRemote___closed__1_once, _init_l_Lake_GitRepo_pruneRemote___closed__1);
v___x_1208_ = lean_array_push(v___x_1207_, v_remote_1203_);
v___x_1209_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1210_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_repo_1204_);
v___x_1212_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1213_ = 1;
v___x_1214_ = 0;
v___x_1215_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1215_, 0, v___x_1209_);
lean_ctor_set(v___x_1215_, 1, v___x_1210_);
lean_ctor_set(v___x_1215_, 2, v___x_1208_);
lean_ctor_set(v___x_1215_, 3, v___x_1211_);
lean_ctor_set(v___x_1215_, 4, v___x_1212_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*5, v___x_1213_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*5 + 1, v___x_1214_);
v___x_1216_ = lean_box(0);
v___x_1217_ = l_Lake_proc(v___x_1215_, v___x_1213_, v___x_1216_, v_a_1205_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote___boxed(lean_object* v_remote_1218_, lean_object* v_repo_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lake_GitRepo_pruneRemote(v_remote_1218_, v_repo_1219_, v_a_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1235_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_1236_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1237_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__1));
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_repo_1233_);
v___x_1239_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1240_ = 1;
v___x_1241_ = 0;
v___x_1242_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1242_, 0, v___x_1236_);
lean_ctor_set(v___x_1242_, 1, v___x_1237_);
lean_ctor_set(v___x_1242_, 2, v___x_1235_);
lean_ctor_set(v___x_1242_, 3, v___x_1238_);
lean_ctor_set(v___x_1242_, 4, v___x_1239_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*5, v___x_1240_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*5 + 1, v___x_1241_);
v___x_1243_ = l_Lake_testProc(v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_1244_, lean_object* v_a_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Lake_GitRepo_hasNoDiff(v_repo_1244_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_1248_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = l_Lake_GitRepo_hasNoDiff(v_repo_1248_);
if (v___x_1250_ == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = 1;
return v___x_1251_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_1253_, lean_object* v_a_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lake_GitRepo_hasDiff(v_repo_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
