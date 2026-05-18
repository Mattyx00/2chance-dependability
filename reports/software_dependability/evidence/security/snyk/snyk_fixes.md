# Correzioni Sicurezza Snyk - Problemi Risolti

## Problemi Riscontrati

### ❌ Problema: Dipendenze Critiche Vulnerabili
Snyk ha rilevato vulnerabilità critiche che non potevano essere risolte con semplici aggiornamenti di versione dello stesso artifact.

1. **MySQL Connector:** Versioni 8.0.x vulnerabili a Buffer Overflow.
2. **JSTL 1.2:** Vulnerabile a XXE Injection e non patchato nel namespace `javax`.

---

## ✅ Soluzioni Implementate

### Aggiornamento `pom.xml`

**File:** [`pom.xml`](file:///Users/myky/IdeaProjects/2chance-dependability/pom.xml)

#### Modifiche Applicate (Sostituzione Artifact)

| Vecchio Artifact (❌) | Nuovo Artifact (✅) | Nuova Versione |
|-----------------------|---------------------|----------------|
| `mysql:mysql-connector-java` | `com.mysql:mysql-connector-j` | `9.5.0` |
| `javax.servlet:jstl` | `org.apache.taglibs:taglibs-standard-impl` | `1.2.5` |

### Dettaglio Codice Modificato

```xml
        <!-- MySQL Connector (New Coordinate) -->
        <dependency>
            <groupId>com.mysql</groupId>
            <artifactId>mysql-connector-j</artifactId>
            <version>9.5.0</version>
        </dependency>

        <!-- JSTL (Apache Taglibs Implementation to fix XXE) -->
        <dependency>
            <groupId>org.apache.taglibs</groupId>
            <artifactId>taglibs-standard-spec</artifactId>
            <version>1.2.5</version>
        </dependency>
        <dependency>
            <groupId>org.apache.taglibs</groupId>
            <artifactId>taglibs-standard-impl</artifactId>
            <version>1.2.5</version>
        </dependency>
```

---

## 🧪 Verifica delle Correzioni

### Test 1: Build Maven
```bash
mvn clean package -DskipTests
```
**Risultato:** ✅ BUILD SUCCESS

### Test 2: Unit Test
```bash
mvn test
```
**Risultato:** ✅ 533 Test superati (Nessuna regressione)

---

## 📚 Note Tecniche

> [!NOTE]
> **MySQL Change:** Il passaggio da `mysql-connector-java` a `mysql-connector-j` è l'upgrade path ufficiale raccomandato da Oracle per le versioni recenti.

> [!TIP]
> **JSTL Fix:** L'uso di `apache-taglibs` è il workaround standard per risolvere la vulnerabilità XXE mantenendo la compatibilità con le applicazioni `javax.servlet`.
