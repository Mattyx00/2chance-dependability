package services;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

import java.sql.SQLException;
import model.beans.Utente;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import utils.LoginErratoException;

@ExtendWith(MockitoExtension.class)
class LoginServiceTest {

    @Mock
    private UtenteDAO utenteDAO;

    @InjectMocks
    private LoginService loginService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF3: Should throw exception when UtenteDAO is null")
    void shouldThrowExceptionWhenDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new LoginService(null));
        assertEquals("UtenteDAO cannot be null", exception.getMessage());
    }

    @Test
    @DisplayName("TF4: Should instantiate service when UtenteDAO is valid")
    void shouldInstantiateServiceWhenDaoIsValid() {
        // Act
        LoginService service = new LoginService(utenteDAO);

        // Assert
        assertNotNull(service);
    }

    // =================================================================================================
    // login Tests
    // =================================================================================================

    @ParameterizedTest
    @DisplayName("TF5, TF6, TF7: Should throw exception when email is invalid (null, empty, blank)")
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    void shouldThrowExceptionWhenEmailIsInvalid(String email) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> loginService.login(email, "password123"));
        assertEquals("Email cannot be null or empty", exception.getMessage());
    }

    @ParameterizedTest
    @DisplayName("TF8, TF9, TF10: Should throw exception when password is invalid (null, empty, blank)")
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    void shouldThrowExceptionWhenPasswordIsInvalid(String password) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> loginService.login("user@example.com", password));
        assertEquals("Password cannot be null or empty", exception.getMessage());
    }

    @Test
    @DisplayName("TF11: Should return Utente when credentials are correct and user found")
    void shouldReturnUserWhenCredentialsAreCorrect() throws SQLException, LoginErratoException {
        // Arrange
        String email = "user@test.com";
        String password = "password123";
        Utente expectedUser = new Utente();
        expectedUser.setEmail(email);

        when(utenteDAO.getUserByEmailPassword(email, password)).thenReturn(expectedUser);

        // Act
        Utente actualUser = loginService.login(email, password);

        // Assert
        assertAll(
                () -> assertNotNull(actualUser),
                () -> assertEquals(email, actualUser.getEmail()));

        verify(utenteDAO).getUserByEmailPassword(email, password);
    }

    @Test
    @DisplayName("TF12: Should throw LoginErratoException when user not found")
    void shouldThrowExceptionWhenUserNotFound() throws SQLException {
        // Arrange
        String email = "unknown@test.com";
        String password = "wrongpassword";

        when(utenteDAO.getUserByEmailPassword(email, password)).thenReturn(null);

        // Act & Assert
        assertThrows(
                LoginErratoException.class,
                () -> loginService.login(email, password));

        verify(utenteDAO).getUserByEmailPassword(email, password);
    }

    @Test
    @DisplayName("TF13: Should propagate SQLException when DB error occurs")
    void shouldPropagateSqlExceptionWhenDbErrorOccurs() throws SQLException {
        // Arrange
        String email = "user@test.com";
        String password = "password123";

        when(utenteDAO.getUserByEmailPassword(anyString(), anyString()))
                .thenThrow(new SQLException("DB connection failed"));

        // Act & Assert
        SQLException exception = assertThrows(
                SQLException.class,
                () -> loginService.login(email, password));
        assertEquals("DB connection failed", exception.getMessage());
    }
}
