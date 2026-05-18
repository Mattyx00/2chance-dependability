# SonarQube Security Analysis

## Overview
This document provides a detailed analysis of the security vulnerabilities identified by SonarQube Cloud and the measures taken to resolve them. The focus was on ensuring robust exception handling across the application's Controller layer to prevent information leakage and unexpected behavior.

### Summary
- **Total Issues Found:** 96
- **Severity:** Low/Minor (Code Quality/Security)
- **Primary Rule Violated:** `java:S1989` ("Exceptions should not be thrown by servlet methods")
- **Status:** 100% Resolved

---

## Detailed Analysis

### Vulnerability: Unhandled Exceptions in Servlets (`java:S1989`)

**Description:**
The SonarQube report highlighted 96 instances where Servlet methods (specifically `doGet`, `doPost`, and `init`) declared that they throw exceptions (such as `IOException`, `ServletException`, `NumberFormatException`, `SQLException`) instead of handling them internally.

**Risk:**
Allowing exceptions to bubble up to the Servlet container can lead to:
1.  **Information Leakage:** Default error pages often display stack traces, revealing internal application details (paths, library versions, logic flow) to potential attackers.
2.  **Poor User Experience:** Users are presented with generic, often ugly, server error pages instead of a controlled error view.
3.  **Denial of Service (DoS):** Unhandled exceptions can leave resources (like database connections) in an inconsistent state if `finally` blocks are missing or bypassed.

**Affected Components:**
Virtually all Servlet controllers were affected, including:
- `EditProfiloServlet`
- `AdminServlet`
- `AggiungiCarrelloServlet`
- `CheckOutServlet`
- `ConfrontaServlet`
- `EditCarrello`
- `FileServlet`
- `landingpage`
- `LoginServlet`
- `logoutServlet`
- `ProdottiPerCategoriaServlet`
- `ProdottoServlet`
- `RecensioniServlet`
- `RegistrazioneServlet`
- `RicercaServlet`
- `UtenteServlet`
- `WishlistServlet`

---

## Solution Implemented

### Robust Exception Handling Pattern

To resolve these issues and satisfy rule `S1989`, we refactored the method entry points in all affected Servlets. We wrapped the core logic in `try-catch` blocks to intercept both checked and runtime exceptions.

#### Before Changes
Methods often declared exceptions in their signature and let them propagate:
```java
protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
    // Logic making calls to Service layer which might throw SQLException
    // Logic parsing parameters which might throw NumberFormatException
    // Logic explicitly calling response.sendError which throws IOException
}
```

#### After Changes
Methods now catch exceptions and handle them gracefully, ensuring the method signature's `throws` clause is either removed (where valid) or effectively neutralized by the catch block preventing escape.

```java
protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
    try {
        // Safe logic execution
        try {
            // Business logic
        } catch (SQLException e) {
            // Handle specific DB errors
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    } catch (Exception e) {
        // Catch-all safety net for unexpected RuntimeExceptions or escaping IOExceptions
        // Log the error (e.printStackTrace() for now, Logger in prod)
        if (!response.isCommitted()) {
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }
}
```

### Specific Key Fixes

1.  **Nested Try-Catch:** In complex Servlets like `FileServlet` and `AdminServlet`, we implemented nested `try-catch` blocks to handle specific exceptions differently from generic ones.
2.  **Response Commit Check:** Added checks for `!response.isCommitted()` before attempting to send an error response in the catch block, preventing `IllegalStateException`.
3.  **Forwarding Logic:** Ensured that `doPost` simply delegates to `doGet` inside a safe block.
4.  **Init Method:** Wrapped initialization logic (e.g., Service instantiation) to catch `SQLException` and rethrow it as `ServletException` with a descriptive message, or handle it if possible.

### Phase 2: Reflected XSS / Exception Leaks in Error handling
Further analysis revealed that calling `response.sendError()` could itself throw `IOException`, leading to additional S1989 violations. To address this cleaner and consistently:

*   **Centralized Utility (`ResponseUtils`):** We introduced a helper class `utils.ResponseUtils` with a `sendError` method. This method encapsulates the check for `isCommitted()` and the `try-catch` block around `sendError`, ensuring safe execution without cluttering the Servlet code.
*   **Refactoring:** 11 Servlets were updated to use this utility, replacing verbose local error handling.

---

## Conclusion

By implementing comprehensive exception handling in the Controller layer, we have:
1.  **Secured the Application:** Prevented stack trace leaks.
2.  **Improved Stability:** Ensured that one failed request does not destabilize the servlet execution.
3.  **Complied with Standards:** Satisfied SonarQube's strict quality and security rules.
