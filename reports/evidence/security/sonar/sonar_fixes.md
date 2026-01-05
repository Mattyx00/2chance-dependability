# SonarQube Fixes Reference

## Summary of Changes
**Vulnerability:** unhandled exceptions in Servlet methods (`java:S1989`).
**Total Files Modified:** 17 Servlets.

## Modified Files
The following files were refactored to include robust `try-catch` blocks:

### Controllers
| File | Change Description |
|------|--------------------|
| `AdminServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `AggiungiCarrelloServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `CheckOutServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `ConfrontaServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `EditCarrello.java` | Wrapped `doGet`, `doPost`, `init`. |
| `EditProfiloServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `FileServlet.java` | Wrapped `doGet`, `doHead`, `processRequest`. Fixed syntax. |
| `landingpage.java` | Wrapped `doGet`, `doPost`, `init`. |
| `LoginServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `logoutServlet.java` | Wrapped `doGet`, `doPost`. |
| `ProdottiPerCategoriaServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `ProdottoServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `RecensioniServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `RegistrazioneServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `RicercaServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `UtenteServlet.java` | Wrapped `doGet`, `doPost`, `init`. |
| `WishlistServlet.java` | Wrapped `doGet`, `doPost`, `init`. |

## Key Patterns Used

**Standard Servlet Method Wrap:**
```java
@Override
protected void doGet(...) throws ServletException, IOException {
    try {
        // Original logic here
    } catch (Exception e) {
        e.printStackTrace();
        if (!response.isCommitted()) response.sendError(500);
    }
}
```

**Init Method Wrap:**
```java
@Override
public void init() throws ServletException {
    try {
        this.service = new Service();
    } catch (SQLException e) {
        throw new ServletException("Init failed", e);
    }
}
```
