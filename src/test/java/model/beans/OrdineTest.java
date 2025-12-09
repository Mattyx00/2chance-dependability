package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.Date;

import static org.junit.jupiter.api.Assertions.*;

class OrdineTest {

    private Ordine order;

    @BeforeEach
    void setUp() {
        order = new Ordine();
    }

    // 2.1 Constructor
    @Test
    @DisplayName("Constructor: should create empty object")
    void testConstructor() {
        assertNotNull(order);
    }

    // 2.2 Method: void setDataOrdine(Date dataOrdine)
    // F1: Set null date -> throws IllegalArgumentException
    @Test
    @DisplayName("setDataOrdine: should throw exception when dataOrdine is null")
    void shouldThrowExceptionWhenSettingNullDataOrdine() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> order.setDataOrdine(null));
        assertEquals("La data dell'ordine non può essere null", exception.getMessage());
    }

    // F2: Set valid date -> Success
    @Test
    @DisplayName("setDataOrdine: should set valid dataOrdine")
    void shouldSetValidDataOrdine() {
        // Arrange
        Date now = new Date();

        // Act
        order.setDataOrdine(now);

        // Assert
        assertEquals(now, order.getDataOrdine());
    }

    // 2.3 Method: void setIndirizzo(String indirizzo)
    // F1 & F2: Set null or empty/whitespace address -> throws
    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   ", "\t", "\n" })
    @DisplayName("setIndirizzo: should throw exception when indirizzo is null, empty or whitespace")
    void shouldThrowExceptionWhenSettingNullOrEmptyIndirizzo(String invalidAddress) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> order.setIndirizzo(invalidAddress));
        assertEquals("L'indirizzo non può essere null o vuoto", exception.getMessage());
    }

    // F3: Set valid address -> succeeds
    @Test
    @DisplayName("setIndirizzo: should set valid indirizzo")
    void shouldSetValidIndirizzo() {
        // Arrange
        String validAddress = "Via Roma, 123";

        // Act
        order.setIndirizzo(validAddress);

        // Assert
        assertEquals(validAddress, order.getIndirizzo());
    }

    // 2.4 Method: void setPrezzoTotale(double prezzoTotale)
    // F1: Set negative price -> throws
    @Test
    @DisplayName("setPrezzoTotale: should throw exception when prezzoTotale is negative")
    void shouldThrowExceptionWhenSettingNegativePrezzoTotale() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> order.setPrezzoTotale(-0.01));
        assertEquals("Il prezzo totale non può essere negativo", exception.getMessage());
    }

    // F2: Set zero price (boundary) -> Success
    @Test
    @DisplayName("setPrezzoTotale: should set zero prezzoTotale")
    void shouldSetZeroPrezzoTotale() {
        // Arrange
        double validPrice = 0.0;

        // Act
        order.setPrezzoTotale(validPrice);

        // Assert
        assertEquals(validPrice, order.getPrezzoTotale(), 0.0001);
    }

    // F3: Set positive price -> Success
    @Test
    @DisplayName("setPrezzoTotale: should set positive prezzoTotale")
    void shouldSetPositivePrezzoTotale() {
        // Arrange
        double validPrice = 99.99;

        // Act
        order.setPrezzoTotale(validPrice);

        // Assert
        assertEquals(validPrice, order.getPrezzoTotale(), 0.0001);
    }

    // 2.5 Method: void setUtente(Utente utente)
    // Derived: F1 Null -> throws
    @Test
    @DisplayName("setUtente: should throw exception when utente is null")
    void shouldThrowExceptionWhenSettingNullUtente() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> order.setUtente(null));
        assertEquals("L'utente non può essere null", exception.getMessage());
    }

    // Derived: F2 Valid -> Success
    @Test
    @DisplayName("setUtente: should set valid utente")
    void shouldSetValidUtente() {
        // Arrange
        Utente utente = new Utente();

        // Act
        order.setUtente(utente);

        // Assert
        assertEquals(utente, order.getUtente());
    }

    // 2.6 Method: void setCarrello(Carrello carrello)
    // Derived: F1 Null -> throws
    @Test
    @DisplayName("setCarrello: should throw exception when carrello is null")
    void shouldThrowExceptionWhenSettingNullCarrello() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> order.setCarrello(null));
        assertEquals("Il carrello non può essere null", exception.getMessage());
    }

    // Derived: F2 Valid -> Success
    @Test
    @DisplayName("setCarrello: should set valid carrello")
    void shouldSetValidCarrello() {
        // Arrange
        Carrello carrello = new Carrello();

        // Act
        order.setCarrello(carrello);

        // Assert
        assertEquals(carrello, order.getCarrello());
    }
}
