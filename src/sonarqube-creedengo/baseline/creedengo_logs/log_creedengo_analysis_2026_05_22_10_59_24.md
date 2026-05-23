# Creedengo (Eco-Design) Violations Report
Generated on: **2026-05-22 10:59:24**
Total Creedengo issues found: **64**

## Summary by Rule

| Rule | Description | Count |
|---|---|---|
| `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | 23 |
| `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | 23 |
| `creedengo-java:GCI74` | Don't use the query SELECT * FROM | 16 |
| `creedengo-java:GCI72` | Avoid SQL request in loop | 2 |

## Detailed Issues List

| # | File | Line | Rule | Message | Severity |
|---|------|------|------|---------|----------|
| 1 | `src/main/java/model/beans/Carrello.java` | 28 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 2 | `src/main/java/model/beans/Carrello.java` | 28 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 3 | `src/main/java/model/beans/Carrello.java` | 72 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 4 | `src/main/java/model/beans/Carrello.java` | 72 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 5 | `src/main/java/model/beans/Carrello.java` | 101 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 6 | `src/main/java/model/beans/Carrello.java` | 101 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 7 | `src/main/java/model/beans/Ordine.java` | 70 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 8 | `src/main/java/model/beans/Ordine.java` | 70 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 9 | `src/main/java/model/beans/Prodotto.java` | 157 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 10 | `src/main/java/model/beans/Prodotto.java` | 157 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 11 | `src/main/java/model/beans/Prodotto.java` | 186 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 12 | `src/main/java/model/beans/Prodotto.java` | 186 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 13 | `src/main/java/model/beans/Prodotto.java` | 229 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 14 | `src/main/java/model/beans/Prodotto.java` | 229 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 15 | `src/main/java/model/beans/Recensione.java` | 47 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 16 | `src/main/java/model/beans/Recensione.java` | 47 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 17 | `src/main/java/model/beans/Recensione.java` | 117 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 18 | `src/main/java/model/beans/Recensione.java` | 117 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 19 | `src/main/java/model/beans/Utente.java` | 71 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 20 | `src/main/java/model/beans/Utente.java` | 71 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 21 | `src/main/java/model/beans/Utente.java` | 95 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 22 | `src/main/java/model/beans/Utente.java` | 95 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 23 | `src/main/java/model/beans/Utente.java` | 119 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 24 | `src/main/java/model/beans/Utente.java` | 119 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 25 | `src/main/java/model/beans/Utente.java` | 143 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 26 | `src/main/java/model/beans/Utente.java` | 143 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 27 | `src/main/java/model/beans/Utente.java` | 199 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 28 | `src/main/java/model/beans/Utente.java` | 199 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 29 | `src/main/java/model/beans/Utente.java` | 251 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 30 | `src/main/java/model/beans/Utente.java` | 251 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 31 | `src/main/java/model/beans/Categoria.java` | 22 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 32 | `src/main/java/model/beans/Categoria.java` | 22 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 33 | `src/main/java/model/beans/Categoria.java` | 50 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 34 | `src/main/java/model/beans/Categoria.java` | 50 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 35 | `src/main/java/model/beans/Specifiche.java` | 23 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 36 | `src/main/java/model/beans/Specifiche.java` | 23 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 37 | `src/main/java/model/beans/Specifiche.java` | 36 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 38 | `src/main/java/model/beans/Specifiche.java` | 36 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 39 | `src/main/java/model/beans/Specifiche.java` | 63 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 40 | `src/main/java/model/beans/Specifiche.java` | 63 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 41 | `src/main/java/model/beans/Specifiche.java` | 89 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 42 | `src/main/java/model/beans/Specifiche.java` | 89 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 43 | `src/main/java/model/dao/OrdineDAO.java` | 37 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 44 | `src/main/java/model/dao/OrdineDAO.java` | 83 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 45 | `src/main/java/model/dao/OrdineDAO.java` | 135 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 46 | `src/main/java/model/dao/OrdineDAO.java` | 295 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 47 | `src/main/java/model/dao/ProdottoDAO.java` | 46 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 48 | `src/main/java/model/dao/ProdottoDAO.java` | 82 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 49 | `src/main/java/model/dao/ProdottoDAO.java` | 120 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 50 | `src/main/java/model/dao/ProdottoDAO.java` | 137 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 51 | `src/main/java/model/dao/RecensioneDAO.java` | 33 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 52 | `src/main/java/model/dao/RecensioneDAO.java` | 51 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 53 | `src/main/java/model/dao/UtenteDAO.java` | 102 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 54 | `src/main/java/model/dao/CategoriaDAO.java` | 32 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 55 | `src/main/java/model/dao/ProdottoDAO.java` | 29 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 56 | `src/main/java/model/dao/UtenteDAO.java` | 25 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 57 | `src/main/java/model/dao/UtenteDAO.java` | 57 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 58 | `src/main/java/model/dao/WishListDAO.java` | 79 | `creedengo-java:GCI74` | Don't use the query SELECT * FROM | CRITICAL |
| 59 | `src/main/java/services/AdminService.java` | 95 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 60 | `src/main/java/services/AdminService.java` | 95 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 61 | `src/main/java/services/AdminService.java` | 370 | `creedengo-java:GCI69` | Do not call a function when declaring a for-type loop | CRITICAL |
| 62 | `src/main/java/services/AdminService.java` | 370 | `creedengo-java:GCI3` | Avoid getting the size of the collection in the loop | CRITICAL |
| 63 | `src/main/java/model/dao/OrdineDAO.java` | 248 | `creedengo-java:GCI72` | Avoid SQL request in loop | CRITICAL |
| 64 | `src/main/java/model/dao/ProdottoDAO.java` | 182 | `creedengo-java:GCI72` | Avoid SQL request in loop | CRITICAL |
